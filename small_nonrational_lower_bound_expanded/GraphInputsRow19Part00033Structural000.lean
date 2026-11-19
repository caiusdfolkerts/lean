module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00033Data
public import GraphInputsRow19Part00033Frames
public import GraphInputsRow19Part00033Leaves
public import GraphInputsRow19Part00033Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 70412230721536, 12983033300779008, 22548578304, 4503599627370496]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 3), (certNat% 4), 1145693263626240, 387234251407360]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 21096879357952, 2603644071444480]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18014337432027136, 54043195662663680, (certNat% 7), 60934848512]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 6), 7893393975803904, 62612570112, 9763800693604352, 351844257759232]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record026
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dc4f2ca9aa5a368d64d8ce8b8ae2785e0fac99a65936539355353362d4b4ad4749d1743db0f2398e5354cd34ce8b92ccb8acab1ae1b26c5b0ed8731e2729c9715c3783c8f13c2f07d2645a4932629165254548d0b41d90cc388d2344c5341c8709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db4db6da4936924924924924d24db69a49249a691249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 32), (facetIndex 43), (facetIndex 58), (facetIndex 71)]))
 (.leaf ([(facetIndex 22), (facetIndex 29), (facetIndex 30), (facetIndex 48)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 56), (facetIndex 63)]))
 (.leaf ([(facetIndex 21), (facetIndex 27), (facetIndex 28), (facetIndex 45)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 51), (facetIndex 57), (facetIndex 61), (facetIndex 62), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 44), (facetIndex 46), (facetIndex 47), (facetIndex 49)]))
 (.branch 8
 (.leaf ([(facetIndex 24), (facetIndex 31), (facetIndex 40)]))
 (.leaf ([(facetIndex 34)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "52550005244445461663600672000080071133007013z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4, 5]
def grouped2_0003 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0004 : List Nat := [6]
def grouped2_0005 : List Nat := [6, 7, 8]
def grouped2_0006 : List Nat := [7]
def grouped2_0007 : List Nat := [7, 8]
def grouped2_0008 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record026" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record026" 35

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record026" "{\"ridges\":[[7,546],[9,578],[16,552],[18,584],[30,546],[31,134],[39,546],[41,578],[44,82],[46,578],[47,546],[47,578],[48,546],[49,578],[56,552],[62,584],[63,552],[63,584],[64,584],[75,106]],\"owners\":[[31,134,[67,68],[2,24,28,29,32,70,72]],[44,82,[66,74],[4,27,34,45,46,72,73]],[7,546,[69,75],[30,39,47,48]],[30,546,[75],[7,39,47,48,69]],[39,546,[],[7,30,47,48,69,75]],[47,546,[69],[7,30,39,48,75]],[48,546,[69,75],[7,30,39,47]],[9,578,[74,75,76],[41,46,47,49]],[41,578,[],[9,46,47,49,74,75,76]],[46,578,[75,76],[9,41,47,49,74]],[47,578,[74,76],[9,41,46,49,75]],[49,578,[74,75],[9,41,46,47,76]],[16,552,[69,75],[39,56,63]],[56,552,[75],[16,39,63,69]],[63,552,[69],[16,39,56,75]],[18,584,[74,75,76],[41,62,63,64]],[62,584,[75,76],[18,41,63,64,74]],[63,584,[74,76],[18,41,62,64,75]],[64,584,[74,75],[18,41,62,63,76]],[75,106,[37],[]]],\"edges\":[[38,[7,16,30,39,47,48,56,63,69,75]],[41,[9,18,41,46,47,49,62,63,64,74,75,76]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record026" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record026\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-9],[-17,-9],[-26,-25],[-27,-5],[-27,-8],[-27,-11],[-27,-15],[-27,-22],[-27,-23],[-27,-24],[-27,-26],[-28,-25],[-28,-27],[-7,23,24],[-13,22,26],[-1,25,27],[-6,27],[-10],[-15,25],[-16,25,27],[-2,26,27,28],[-12],[-14,27,28],[-15,26,28],[-17,26,27],[-3,25,27],[-18,27],[-20,25],[-4,26,27,28],[-19,27,28],[-20,26,28],[-21,26,27],[-27,9],[-29,12,13,14,15,17],[-30,5,7,11],[-31,8],[-32,30,31],[-33,29,32],[-34,33],[-35,34],[35],[1,3,6,10,15,16,18,20,25,27],[2,4,12,14,15,17,19,20,21,26,27,28]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":46,\"b\":37},{\"tag\":\"incompatible\",\"a\":49,\"b\":37},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":75,\"b\":24},{\"tag\":\"incompatible\",\"a\":75,\"b\":34},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":47},{\"tag\":\"incompatible\",\"a\":75,\"b\":66},{\"tag\":\"incompatible\",\"a\":75,\"b\":67},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":69},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"mate\",\"ridge\":134,\"a\":31,\"owners\":[67,68]},{\"tag\":\"mate\",\"ridge\":82,\"a\":44,\"owners\":[66,74]},{\"tag\":\"mate\",\"ridge\":546,\"a\":7,\"owners\":[69,75]},{\"tag\":\"mate\",\"ridge\":546,\"a\":30,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":546,\"a\":39,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":546,\"a\":47,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":546,\"a\":48,\"owners\":[69,75]},{\"tag\":\"mate\",\"ridge\":578,\"a\":9,\"owners\":[74,75,76]},{\"tag\":\"mate\",\"ridge\":578,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":578,\"a\":46,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":578,\"a\":47,\"owners\":[74,76]},{\"tag\":\"mate\",\"ridge\":578,\"a\":49,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":552,\"a\":16,\"owners\":[69,75]},{\"tag\":\"mate\",\"ridge\":552,\"a\":56,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":552,\"a\":63,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":584,\"a\":18,\"owners\":[74,75,76]},{\"tag\":\"mate\",\"ridge\":584,\"a\":62,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":584,\"a\":63,\"owners\":[74,76]},{\"tag\":\"mate\",\"ridge\":584,\"a\":64,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":106,\"a\":75,\"owners\":[37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[41,44,46,47,49],\"full_literals\":[-29,12,13,14,15,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[24,31,40],\"full_literals\":[-30,5,7,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[34],\"full_literals\":[-31,8]},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,30,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-33,29,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[7,16,30,39,47,48,56,63,69,75]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[9,18,41,46,47,49,62,63,64,74,75,76]}]}"
  "44 -29 13 14 15 17 0 22 34 0\n45 34 0 41 40 0\n46 33 0 45 39 0\n47 1 3 6 15 16 18 20 25 27 0 18 42 0\n48 2 4 14 15 17 19 20 21 26 27 28 0 22 43 0\n49 26 27 28 0 30 23 24 31 25 32 21 29 48 0\n50 27 18 28 0 17 49 3 19 28 16 26 20 47 0\n51 -28 0 12 13 19 28 16 26 20 17 27 47 0\n52 27 0 51 27 50 0\n53 -5 0 52 4 0\n54 -8 0 52 5 0\n55 -11 0 52 6 0\n56 -15 0 52 7 0\n57 -22 0 52 8 0\n58 -23 0 52 9 0\n59 -24 0 52 10 0\n60 -26 0 52 11 0\n61 9 0 52 33 0\n62 -31 0 54 36 0\n63 -13 0 57 60 15 0\n64 -7 0 58 59 14 0\n65 -14 0 61 1 0\n66 -17 0 61 2 0\n67 -30 0 64 53 55 35 0\n68 -29 0 65 63 56 66 44 0\n69 -32 0 67 62 37 0\n70 0 68 69 46 38 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record026

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record093
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9e2742f07c9a93a2e966659362d8ce2b86e2783ecc6719a699966394e47999565656558d5351d4cd1b49d1743d98d6364d3392ccb8ad2b1ad1b26c3b61d4731d2719d1725c3723c4f0bc1f9a2384d06a4986692619265152548b12d0721c47"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4db4da69b69b6d249b6d369b69b6db49b4d349249349b249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 57), (facetIndex 71), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 21), (facetIndex 42), (facetIndex 49)]))
 (.leaf ([(facetIndex 23), (facetIndex 62), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 18), (facetIndex 31), (facetIndex 34), (facetIndex 35)]))
 (.leaf ([(facetIndex 22), (facetIndex 29), (facetIndex 66)])))
 (.branch 7
 (.leaf ([(facetIndex 19), (facetIndex 25), (facetIndex 26), (facetIndex 27)]))
 (.leaf ([(facetIndex 24), (facetIndex 46)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2002031400c00080000101c0080000900828db7750d00000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 45), (facetIndex 48)]))
 (.leaf ([(facetIndex 52), (facetIndex 72), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 16), (facetIndex 20), (facetIndex 30), (facetIndex 37), (facetIndex 65)]))
 (.leaf ([(facetIndex 17), (facetIndex 44), (facetIndex 60), (facetIndex 63)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 61), (facetIndex 64), (facetIndex 73)]))
 (.leaf ([(facetIndex 28), (facetIndex 67), (facetIndex 69), (facetIndex 70)])))
 (.branch 7
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 36), (facetIndex 38), (facetIndex 43), (facetIndex 47), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 39), (facetIndex 50), (facetIndex 51), (facetIndex 53)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "61168a14623d80039fc0c03c04f9603608500000201a000000000000"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
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
def grouped3_0017 : List Nat := [0, 1, 2, 3]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [4, 5, 6, 7]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7]
def grouped3_0029 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record093" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record093" 82

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record093" "{\"ridges\":[[1,134],[4,138],[5,148],[7,152],[14,560],[19,134],[19,138],[21,134],[21,148],[22,259],[22,273],[23,100],[24,259],[24,290],[25,131],[27,134],[29,138],[29,152],[34,138],[42,148],[42,152],[44,204],[46,273],[46,304],[47,549],[49,148],[54,529],[54,560],[55,529],[56,152],[58,113],[59,801],[61,30],[62,100],[63,172],[64,204],[66,52],[66,290],[66,304],[67,402],[69,178],[70,56],[73,172],[75,608]],\"owners\":[[25,131,[4,29,37],[1,21,27,34]],[1,134,[61,63,64,65,67],[19,21,25,27]],[19,134,[65,67],[1,21,25,27,61,63,64]],[21,134,[63,64],[1,19,25,27,61,65,67]],[27,134,[61,63,64,65],[1,19,21,25,67]],[22,259,[32,38],[2,24,26,27,30,36,37]],[24,259,[30,37],[2,22,26,27,32,36,38]],[4,138,[61,63,64,69],[19,29,34]],[19,138,[69],[4,29,34,61,63,64]],[29,138,[63,64],[4,19,34,61,69]],[34,138,[61,63,69],[4,19,29,64]],[5,148,[61,65,67,73],[21,42,49]],[21,148,[73],[5,42,49,61,65,67]],[42,148,[65,67],[5,21,49,61,73]],[49,148,[61,65,73],[5,21,42,67]],[22,273,[53,59],[6,30,36,37,46,49]],[46,273,[30,37],[6,22,36,49,53,59]],[7,152,[61,69,73],[29,42,56]],[29,152,[73],[7,42,56,61,69]],[42,152,[69],[7,29,56,61,73]],[56,152,[61,69,73],[7,29,42]],[54,529,[48],[8,47,55,56,58,59]],[55,529,[47,59],[8,48,54,56,58]],[23,100,[72,74],[10,43,45,50,51,62,68]],[62,100,[45,50,51,74],[10,23,43,68,72]],[24,290,[70],[11,32,36,38,66,68]],[66,290,[32,38],[11,24,36,68,70]],[66,52,[40,45,47,72,73,74],[13,20,46,60,65]],[46,304,[70],[13,36,53,59,66]],[66,304,[53,59],[13,36,46,70]],[70,56,[14,40,52,54,72,73,75],[28,53,60,69]],[14,560,[47,58,59,74],[54,75]],[54,560,[74],[14,47,58,59,75]],[75,608,[39,51],[15,57,58,71,74]],[61,30,[16,60],[]],[67,402,[37],[]],[44,204,[64],[]],[64,204,[44],[]],[58,113,[45,52],[]],[47,549,[51],[]],[59,801,[],[]],[63,172,[73],[]],[73,172,[63],[]],[69,178,[65],[]]],\"edges\":[[21,[1,5,19,21,25,27,42,44,49,61,63,64,65,67,73]],[27,[4,7,19,29,34,42,44,56,61,63,64,69,73]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record093" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record093\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-9],[-12,-11],[-13,-11],[-14,-11],[-15,-8],[-23,-15],[-26,-9],[-26,-21],[-26,-22],[-27,-26],[-29,-9],[-29,-22],[-29,-26],[-29,-27],[-29,-28],[-30,-11],[-31,-11],[-31,-26],[-34,-17],[-34,-20],[-36,-15],[-36,-33],[-45,-11],[-45,-26],[-46,-11],[-46,-26],[-47,-11],[-47,-42],[-48,-9],[-48,-16],[-48,-19],[-48,-45],[-49,-8],[-49,-15],[-49,-44],[-51,-41],[-12,2,15,19],[-1,40,42,43,44,46],[-7,44,46],[-8,42,43],[-14,40,42,43,44],[-9,17,20],[-11,16,19],[-2,40,42,43,48],[-7,48],[-15,42,43],[-18,40,42,48],[-3,40,44,46,51],[-8,51],[-23,44,46],[-29,40,44,51],[-9,33,38],[-26,16,19],[-4,40,48,51],[-15,51],[-23,48],[-36,40,48,51],[-34,28],[-35,27,38],[-10,50,52],[-41,25,30,31,52],[-11,49],[-45,17,20],[-45,22,25,27,50,51,52],[-26,49],[-45,33,38],[-49,5,22,32,34,50,51,53],[-5,27,37,38,52],[-34,52],[-53,21,31],[-40,6,39],[-46,19],[-24,43],[-43,24],[-37,25,32],[-27,31],[-38],[-42,51],[-51,42],[-48,44],[-54,34,35,36],[-55,8,23,29],[-56,10,41,47],[-57,9,15,45],[-58,7,12,13,14],[-59,11,26],[-60,54],[-61,55],[-61,56],[-62,60],[-62,61],[-63,57],[-64,58],[-64,59],[-65,63,64],[-66,63],[-66,64],[-67,62,66],[-67,65],[67],[-25,68],[-32,69],[-50,69],[-52,69],[-6,70],[-16,70],[-19,70],[-44,70],[-24,71],[-39,71],[-42,71],[-40,72],[-43,72],[-51,72],[-27,73],[-31,74],[-69,75],[-68,75],[-71,76],[-70,76],[-70,-71,77],[-77,78],[-75,-76,78],[-72,79],[-73,-74,80],[-79,-80,81],[-78,-81,82],[-82],[1,3,7,8,12,14,23,24,29,40,42,43,44,46,51],[2,4,7,15,18,23,24,36,40,42,43,48,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":22},{\"tag\":\"incompatible\",\"a\":25,\"b\":24},{\"tag\":\"incompatible\",\"a\":26,\"b\":24},{\"tag\":\"incompatible\",\"a\":27,\"b\":24},{\"tag\":\"incompatible\",\"a\":29,\"b\":21},{\"tag\":\"incompatible\",\"a\":42,\"b\":29},{\"tag\":\"incompatible\",\"a\":46,\"b\":22},{\"tag\":\"incompatible\",\"a\":46,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":22},{\"tag\":\"incompatible\",\"a\":49,\"b\":40},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":24},{\"tag\":\"incompatible\",\"a\":51,\"b\":24},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":32},{\"tag\":\"incompatible\",\"a\":54,\"b\":38},{\"tag\":\"incompatible\",\"a\":56,\"b\":29},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":66,\"b\":24},{\"tag\":\"incompatible\",\"a\":66,\"b\":46},{\"tag\":\"incompatible\",\"a\":67,\"b\":24},{\"tag\":\"incompatible\",\"a\":67,\"b\":46},{\"tag\":\"incompatible\",\"a\":68,\"b\":24},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":22},{\"tag\":\"incompatible\",\"a\":69,\"b\":30},{\"tag\":\"incompatible\",\"a\":69,\"b\":37},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":21},{\"tag\":\"incompatible\",\"a\":70,\"b\":29},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":73,\"b\":62},{\"tag\":\"mate\",\"ridge\":131,\"a\":25,\"owners\":[4,29,37]},{\"tag\":\"mate\",\"ridge\":134,\"a\":1,\"owners\":[61,63,64,65,67]},{\"tag\":\"mate\",\"ridge\":134,\"a\":19,\"owners\":[65,67]},{\"tag\":\"mate\",\"ridge\":134,\"a\":21,\"owners\":[63,64]},{\"tag\":\"mate\",\"ridge\":134,\"a\":27,\"owners\":[61,63,64,65]},{\"tag\":\"mate\",\"ridge\":259,\"a\":22,\"owners\":[32,38]},{\"tag\":\"mate\",\"ridge\":259,\"a\":24,\"owners\":[30,37]},{\"tag\":\"mate\",\"ridge\":138,\"a\":4,\"owners\":[61,63,64,69]},{\"tag\":\"mate\",\"ridge\":138,\"a\":19,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":138,\"a\":29,\"owners\":[63,64]},{\"tag\":\"mate\",\"ridge\":138,\"a\":34,\"owners\":[61,63,69]},{\"tag\":\"mate\",\"ridge\":148,\"a\":5,\"owners\":[61,65,67,73]},{\"tag\":\"mate\",\"ridge\":148,\"a\":21,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":148,\"a\":42,\"owners\":[65,67]},{\"tag\":\"mate\",\"ridge\":148,\"a\":49,\"owners\":[61,65,73]},{\"tag\":\"mate\",\"ridge\":273,\"a\":22,\"owners\":[53,59]},{\"tag\":\"mate\",\"ridge\":273,\"a\":46,\"owners\":[30,37]},{\"tag\":\"mate\",\"ridge\":152,\"a\":7,\"owners\":[61,69,73]},{\"tag\":\"mate\",\"ridge\":152,\"a\":29,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":152,\"a\":42,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":152,\"a\":56,\"owners\":[61,69,73]},{\"tag\":\"mate\",\"ridge\":529,\"a\":54,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":529,\"a\":55,\"owners\":[47,59]},{\"tag\":\"mate\",\"ridge\":100,\"a\":23,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":100,\"a\":62,\"owners\":[45,50,51,74]},{\"tag\":\"mate\",\"ridge\":290,\"a\":24,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":290,\"a\":66,\"owners\":[32,38]},{\"tag\":\"mate\",\"ridge\":52,\"a\":66,\"owners\":[40,45,47,72,73,74]},{\"tag\":\"mate\",\"ridge\":304,\"a\":46,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":304,\"a\":66,\"owners\":[53,59]},{\"tag\":\"mate\",\"ridge\":56,\"a\":70,\"owners\":[14,40,52,54,72,73,75]},{\"tag\":\"mate\",\"ridge\":560,\"a\":14,\"owners\":[47,58,59,74]},{\"tag\":\"mate\",\"ridge\":560,\"a\":54,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":608,\"a\":75,\"owners\":[39,51]},{\"tag\":\"mate\",\"ridge\":30,\"a\":61,\"owners\":[16,60]},{\"tag\":\"mate\",\"ridge\":402,\"a\":67,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":204,\"a\":44,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":204,\"a\":64,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":113,\"a\":58,\"owners\":[45,52]},{\"tag\":\"mate\",\"ridge\":549,\"a\":47,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":801,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":172,\"a\":63,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":172,\"a\":73,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":178,\"a\":69,\"owners\":[65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[54,55,56],\"full_literals\":[-54,34,35,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[21,42,49],\"full_literals\":[-55,8,23,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[23,62,68],\"full_literals\":[-56,10,41,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[22,29,66],\"full_literals\":[-57,9,15,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[19,25,26,27],\"full_literals\":[-58,7,12,13,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[24,46],\"full_literals\":[-59,11,26]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,63,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-67,62,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":45,\"full_literals\":[-25,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":52,\"full_literals\":[-32,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-50,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-52,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":16,\"full_literals\":[-6,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":30,\"full_literals\":[-16,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":37,\"full_literals\":[-19,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-44,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":44,\"full_literals\":[-24,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":60,\"full_literals\":[-39,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-42,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-40,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-43,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-51,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":47,\"full_literals\":[-27,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":51,\"full_literals\":[-31,74]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-71,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-74,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-79,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-78,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":21,\"owners\":[1,5,19,21,25,27,42,44,49,61,63,64,65,67,73]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[4,7,19,29,34,42,44,56,61,63,64,69,73]}]}"
  "131 65 0 100 99 0\n132 76 0 119 120 109 110 111 105 107 108 74 71 40 46 79 41 72 39 50 80 51 38 44 48 37 129 0\n133 -48 -57 15 0 29 32 84 0\n134 48 72 0 114 78 55 113 73 112 45 56 57 47 54 44 130 0\n135 72 0 131 114 55 134 30 31 133 43 53 92 86 95 94 0\n136 -51 78 0 132 100 123 117 104 103 60 122 36 79 28 111 83 121 89 106 107 91 43 53 98 86 97 94 0\n137 -11 -57 15 0 1 23 84 0\n138 -66 15 0 96 97 92 94 137 86 7 24 84 0\n139 -26 78 0 132 77 136 123 117 102 118 101 75 104 69 103 8 9 10 18 65 70 68 67 0\n140 -11 78 0 132 100 136 55 138 98 91 89 123 117 104 103 60 118 101 16 17 27 61 83 0\n141 78 0 132 100 131 123 117 118 103 104 101 136 49 55 138 98 91 88 139 140 86 94 95 92 133 56 82 11 12 14 84 64 0\n142 79 0 135 124 0\n143 -81 0 141 128 127 0\n144 -80 0 143 142 126 0\n145 64 35 34 0 131 100 77 97 95 98 92 90 87 81 21 22 52 66 84 0\n146 -64 26 0 93 94 86 2 3 4 25 62 85 35 39 0\n147 -27 0 144 76 115 116 125 0\n148 -35 0 147 77 59 0\n149 64 0 131 100 148 97 95 98 92 91 88 145 19 20 58 42 63 15 84 5 6 82 0\n150 26 0 149 146 0\n151 -29 0 150 13 0\n152 -46 0 150 26 0\n153 49 0 150 65 0\n154 -8 0 153 33 0\n155 -15 0 153 34 0\n156 -44 0 153 35 0\n157 -66 0 155 138 0\n158 -23 0 156 152 50 0\n159 62 0 157 100 98 0\n160 -55 0 158 151 154 82 0\n161 61 0 159 91 0\n162 0 161 160 88 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record093
