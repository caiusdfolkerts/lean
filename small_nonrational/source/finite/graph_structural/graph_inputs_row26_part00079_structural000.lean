module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00079Data
public import GraphInputsRow26Part00079Frames
public import GraphInputsRow26Part00079Leaves
public import GraphInputsRow26Part00079Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016
def vertexColumn : Fields := ⟨10, hexnat% "1d86e15c3713c2f1e2749b26ab1aa699a4e8ba598e695956359362da2e4b8ae8791e2783e785d1725a9c6699665593656539655554d5534cd8b52d2b61d4749d175c368d6338f13a4d9394d5334f0ba2d8b8ad2b2ae1b46c9b91d4731e2749ca719e1745c9715e0f43c8f0bc1f8715234a16159292a60d0b54330d2328e0711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4db6db6d24db6d36db69b6db6db6d249b6924db6936da4db4924926d26d3249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10200001458600fb300000", hexnat% "802800000000000000000000", hexnat% "400280000000020000", 563053099745280]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000040038780185e020000", hexnat% "20000040000001100000", 2686451712, hexnat% "3800000000000000000000", 6597069766656]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [162692537613549568, hexnat% "2020000000000001000000", 1548112942333952, hexnat% "400180001800020000", hexnat% "801800000000060000200000", 2617245696]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "23c9c9ca5a8ea568da8e87a719663995635a361d98e8b92e2ba1e4789e0fa71725693a559366391e5c5594e5554d58d4756362d4b4ad8751d2743d70e6358ce394d5334e331cd8b52ccb8ad2b2ac6b86d1b26c5b0ef07a1d8751cc749ca719d1725c570de0f89a164388e0b81e896154348d0b41d50cc388c6384c5342c8b0ac1b81d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6db69a4924936db6db6db4d2492492492492492492492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.branch 2
 (.leaf ([(facetIndex 29), (facetIndex 41), (facetIndex 53), (facetIndex 54), (facetIndex 71), (facetIndex 85), (facetIndex 94)]))
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 89), (facetIndex 90), (facetIndex 91), (facetIndex 92)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 40)])))
 (.branch 6
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 52)]))
 (.leaf ([(facetIndex 45), (facetIndex 49)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4249248800000000020000001b6db64db75b75b4c924924908z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 70), (facetIndex 77), (facetIndex 78), (facetIndex 84)]))
 (.branch 2
 (.leaf ([(facetIndex 93), (facetIndex 100), (facetIndex 101), (facetIndex 107)]))
 (.leaf ([(facetIndex 108)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83)])))
 (.branch 6
 (.leaf ([(facetIndex 95), (facetIndex 96), (facetIndex 97), (facetIndex 98), (facetIndex 99)]))
 (.leaf ([(facetIndex 102), (facetIndex 103), (facetIndex 104), (facetIndex 105), (facetIndex 106)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "23b6d89b6da080000009248036dbz36;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2]
def grouped2_0002 : List Nat := [3]
def grouped2_0003 : List Nat := [3, 4]
def grouped2_0004 : List Nat := [3, 4, 5, 6]
def grouped2_0005 : List Nat := [4]
def grouped2_0006 : List Nat := [5]
def grouped2_0007 : List Nat := [5, 6]
def grouped2_0008 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":4}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record006" 61

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record006" "{\"ridges\":[[6,11],[7,11],[16,25],[17,41],[22,26],[23,42],[45,11],[49,11],[50,11],[51,11],[62,25],[62,41],[63,25],[64,25],[66,41],[67,41],[85,26],[85,42],[86,26],[87,26],[89,42],[90,42],[102,216],[103,344],[104,232],[105,360]],\"owners\":[[16,25,[6,41,42,43,44,45,77,78,79,80],[62,63,64,65]],[62,25,[6,42,43,44,45,79,80],[16,41,63,64,65,77,78]],[63,25,[6,41,42,44,45,77,78,80],[16,43,62,64,65,79]],[64,25,[6,41,42,43,45,77,78,79],[16,44,62,63,65,80]],[22,26,[6,41,42,43,44,45,100,101,102,103],[85,86,87,88]],[85,26,[6,42,43,44,45,102,103],[22,41,86,87,88,100,101]],[86,26,[6,41,42,44,45,100,101,103],[22,43,85,87,88,102]],[87,26,[6,41,42,43,45,100,101,102],[22,44,85,86,88,103]],[17,41,[7,41,46,47,48,49,77,78,81,82],[62,66,67,68]],[62,41,[7,46,47,48,49,81,82],[17,41,66,67,68,77,78]],[66,41,[7,41,46,48,49,77,78,82],[17,47,62,67,68,81]],[67,41,[7,41,46,47,49,77,78,81],[17,48,62,66,68,82]],[23,42,[7,41,46,47,48,49,100,101,104,105],[85,89,90,91]],[85,42,[7,46,47,48,49,104,105],[23,41,89,90,91,100,101]],[89,42,[7,41,46,48,49,100,101,105],[23,47,85,90,91,104]],[90,42,[7,41,46,47,49,100,101,104],[23,48,85,89,91,105]],[102,216,[79],[]],[103,344,[80],[]],[104,232,[81],[]],[105,360,[82],[]]],\"edges\":[[24,[6,16,22,41,42,43,44,45,62,63,64,65,77,78,79,80,85,86,87,88,100,101,102,103,108]],[25,[7,17,23,41,46,47,48,49,62,66,67,68,77,78,81,82,85,89,90,91,100,101,104,105,108]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-8],[-11,-9],[-11,-10],[-13,-11],[-14,-11],[-15,-9],[-15,-10],[-15,-11],[-15,-12],[-15,-13],[-15,-14],[-16,-7],[-17,-7],[-18,-11],[-18,-15],[-19,-8],[-19,-11],[-20,-8],[-20,-11],[-21,-8],[-21,-11],[-22,-8],[-22,-12],[-23,-8],[-23,-12],[-24,-12],[-24,-15],[-25,-8],[-25,-12],[-29,-15],[-32,-11],[-33,-16],[-33,-17],[-34,-11],[-34,-15],[-35,-8],[-35,-16],[-35,-17],[-36,-8],[-36,-16],[-36,-17],[-37,-8],[-37,-16],[-37,-17],[-38,-8],[-38,-16],[-38,-17],[-39,-8],[-39,-16],[-39,-17],[-43,-15],[-46,-11],[-47,-16],[-47,-17],[-48,-11],[-48,-15],[-53,-11],[-53,-15],[-1,-15,-16],[-1,-15,-17],[-2,-11,-16],[-2,-11,-17],[-3,1,7,8,9,10,11,33,34,35,36],[-26,1,8,9,10,11,35,36],[-27,1,7,8,10,11,33,34,36],[-28,1,7,8,9,11,33,34,35],[-5,1,7,8,9,10,11,47,48,49,50],[-40,1,8,9,10,11,49,50],[-41,1,7,8,10,11,47,48,50],[-42,1,7,8,9,11,47,48,49],[-4,2,7,12,13,14,15,33,34,37,38],[-26,2,12,13,14,15,37,38],[-30,2,7,12,14,15,33,34,38],[-31,2,7,12,13,15,33,34,37],[-6,2,7,12,13,14,15,47,48,51,52],[-40,2,12,13,14,15,51,52],[-44,2,7,12,14,15,47,48,52],[-45,2,7,12,13,15,47,48,51],[-49,35],[-50,36],[-51,37],[-52,38],[-54,19,20,21,22,23,24,25],[-55,8,9,10,12,13,14,16,17,18],[-56,11,15],[-57,54],[-58,55],[-58,56],[-59,57],[-59,58],[-60,59],[60],[-61,35,36,37,38,39],[-35,61],[-36,61],[-37,61],[-38,61],[1,3,5,7,8,9,10,11,26,27,28,29,33,34,35,36,40,41,42,43,47,48,49,50,53],[2,4,6,7,12,13,14,15,26,30,31,32,33,34,37,38,40,44,45,46,47,48,51,52,53]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":55,\"b\":42},{\"tag\":\"incompatible\",\"a\":55,\"b\":45},{\"tag\":\"incompatible\",\"a\":56,\"b\":42},{\"tag\":\"incompatible\",\"a\":56,\"b\":45},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":45},{\"tag\":\"incompatible\",\"a\":58,\"b\":42},{\"tag\":\"incompatible\",\"a\":58,\"b\":46},{\"tag\":\"incompatible\",\"a\":59,\"b\":42},{\"tag\":\"incompatible\",\"a\":59,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":49},{\"tag\":\"incompatible\",\"a\":61,\"b\":42},{\"tag\":\"incompatible\",\"a\":61,\"b\":46},{\"tag\":\"incompatible\",\"a\":65,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":45},{\"tag\":\"incompatible\",\"a\":77,\"b\":50},{\"tag\":\"incompatible\",\"a\":77,\"b\":51},{\"tag\":\"incompatible\",\"a\":78,\"b\":45},{\"tag\":\"incompatible\",\"a\":78,\"b\":49},{\"tag\":\"incompatible\",\"a\":79,\"b\":42},{\"tag\":\"incompatible\",\"a\":79,\"b\":50},{\"tag\":\"incompatible\",\"a\":79,\"b\":51},{\"tag\":\"incompatible\",\"a\":80,\"b\":42},{\"tag\":\"incompatible\",\"a\":80,\"b\":50},{\"tag\":\"incompatible\",\"a\":80,\"b\":51},{\"tag\":\"incompatible\",\"a\":81,\"b\":42},{\"tag\":\"incompatible\",\"a\":81,\"b\":50},{\"tag\":\"incompatible\",\"a\":81,\"b\":51},{\"tag\":\"incompatible\",\"a\":82,\"b\":42},{\"tag\":\"incompatible\",\"a\":82,\"b\":50},{\"tag\":\"incompatible\",\"a\":82,\"b\":51},{\"tag\":\"incompatible\",\"a\":83,\"b\":42},{\"tag\":\"incompatible\",\"a\":83,\"b\":50},{\"tag\":\"incompatible\",\"a\":83,\"b\":51},{\"tag\":\"incompatible\",\"a\":88,\"b\":49},{\"tag\":\"incompatible\",\"a\":91,\"b\":45},{\"tag\":\"incompatible\",\"a\":100,\"b\":50},{\"tag\":\"incompatible\",\"a\":100,\"b\":51},{\"tag\":\"incompatible\",\"a\":101,\"b\":45},{\"tag\":\"incompatible\",\"a\":101,\"b\":49},{\"tag\":\"incompatible\",\"a\":108,\"b\":45},{\"tag\":\"incompatible\",\"a\":108,\"b\":49},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[6,49,50]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[6,49,51]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[7,45,50]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[7,45,51]},{\"tag\":\"mate\",\"ridge\":25,\"a\":16,\"owners\":[6,41,42,43,44,45,77,78,79,80]},{\"tag\":\"mate\",\"ridge\":25,\"a\":62,\"owners\":[6,42,43,44,45,79,80]},{\"tag\":\"mate\",\"ridge\":25,\"a\":63,\"owners\":[6,41,42,44,45,77,78,80]},{\"tag\":\"mate\",\"ridge\":25,\"a\":64,\"owners\":[6,41,42,43,45,77,78,79]},{\"tag\":\"mate\",\"ridge\":26,\"a\":22,\"owners\":[6,41,42,43,44,45,100,101,102,103]},{\"tag\":\"mate\",\"ridge\":26,\"a\":85,\"owners\":[6,42,43,44,45,102,103]},{\"tag\":\"mate\",\"ridge\":26,\"a\":86,\"owners\":[6,41,42,44,45,100,101,103]},{\"tag\":\"mate\",\"ridge\":26,\"a\":87,\"owners\":[6,41,42,43,45,100,101,102]},{\"tag\":\"mate\",\"ridge\":41,\"a\":17,\"owners\":[7,41,46,47,48,49,77,78,81,82]},{\"tag\":\"mate\",\"ridge\":41,\"a\":62,\"owners\":[7,46,47,48,49,81,82]},{\"tag\":\"mate\",\"ridge\":41,\"a\":66,\"owners\":[7,41,46,48,49,77,78,82]},{\"tag\":\"mate\",\"ridge\":41,\"a\":67,\"owners\":[7,41,46,47,49,77,78,81]},{\"tag\":\"mate\",\"ridge\":42,\"a\":23,\"owners\":[7,41,46,47,48,49,100,101,104,105]},{\"tag\":\"mate\",\"ridge\":42,\"a\":85,\"owners\":[7,46,47,48,49,104,105]},{\"tag\":\"mate\",\"ridge\":42,\"a\":89,\"owners\":[7,41,46,48,49,100,101,105]},{\"tag\":\"mate\",\"ridge\":42,\"a\":90,\"owners\":[7,41,46,47,49,100,101,104]},{\"tag\":\"mate\",\"ridge\":216,\"a\":102,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":344,\"a\":103,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":232,\"a\":104,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":360,\"a\":105,\"owners\":[82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[55,56,57,58,59,60,61],\"full_literals\":[-54,19,20,21,22,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[42,43,44,46,47,48,50,51,52],\"full_literals\":[-55,8,9,10,12,13,14,16,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[45,49],\"full_literals\":[-56,11,15]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[79,80,81,82,83],\"full_literals\":[-61,35,36,37,38,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-35,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-36,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-37,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-38,61]},{\"tag\":\"edge\",\"edge\":24,\"owners\":[6,16,22,41,42,43,44,45,62,63,64,65,77,78,79,80,85,86,87,88,100,101,102,103,108]},{\"tag\":\"edge\",\"edge\":25,\"owners\":[7,17,23,41,46,47,48,49,62,66,67,68,77,78,81,82,85,89,90,91,100,101,104,105,108]}]}"
  "p cnf 61 99\n-11 -8 0\n-11 -9 0\n-11 -10 0\n-13 -11 0\n-14 -11 0\n-15 -9 0\n-15 -10 0\n-15 -11 0\n-15 -12 0\n-15 -13 0\n-15 -14 0\n-16 -7 0\n-17 -7 0\n-18 -11 0\n-18 -15 0\n-19 -8 0\n-19 -11 0\n-20 -8 0\n-20 -11 0\n-21 -8 0\n-21 -11 0\n-22 -8 0\n-22 -12 0\n-23 -8 0\n-23 -12 0\n-24 -12 0\n-24 -15 0\n-25 -8 0\n-25 -12 0\n-29 -15 0\n-32 -11 0\n-33 -16 0\n-33 -17 0\n-34 -11 0\n-34 -15 0\n-35 -8 0\n-35 -16 0\n-35 -17 0\n-36 -8 0\n-36 -16 0\n-36 -17 0\n-37 -8 0\n-37 -16 0\n-37 -17 0\n-38 -8 0\n-38 -16 0\n-38 -17 0\n-39 -8 0\n-39 -16 0\n-39 -17 0\n-43 -15 0\n-46 -11 0\n-47 -16 0\n-47 -17 0\n-48 -11 0\n-48 -15 0\n-53 -11 0\n-53 -15 0\n-1 -15 -16 0\n-1 -15 -17 0\n-2 -11 -16 0\n-2 -11 -17 0\n-3 1 7 8 9 10 11 33 34 35 36 0\n-26 1 8 9 10 11 35 36 0\n-27 1 7 8 10 11 33 34 36 0\n-28 1 7 8 9 11 33 34 35 0\n-5 1 7 8 9 10 11 47 48 49 50 0\n-40 1 8 9 10 11 49 50 0\n-41 1 7 8 10 11 47 48 50 0\n-42 1 7 8 9 11 47 48 49 0\n-4 2 7 12 13 14 15 33 34 37 38 0\n-26 2 12 13 14 15 37 38 0\n-30 2 7 12 14 15 33 34 38 0\n-31 2 7 12 13 15 33 34 37 0\n-6 2 7 12 13 14 15 47 48 51 52 0\n-40 2 12 13 14 15 51 52 0\n-44 2 7 12 14 15 47 48 52 0\n-45 2 7 12 13 15 47 48 51 0\n-49 35 0\n-50 36 0\n-51 37 0\n-52 38 0\n-54 19 20 21 22 23 24 25 0\n-55 8 9 10 12 13 14 16 17 18 0\n-56 11 15 0\n-57 54 0\n-58 55 0\n-58 56 0\n-59 57 0\n-59 58 0\n-60 59 0\n60 0\n-61 35 36 37 38 39 0\n-35 61 0\n-36 61 0\n-37 61 0\n-38 61 0\n1 3 5 7 8 9 10 11 26 27 28 29 33 34 35 36 40 41 42 43 47 48 49 50 53 0\n2 4 6 7 12 13 14 15 26 30 31 32 33 34 37 38 40 44 45 46 47 48 51 52 53 0\n"
  "100 59 0 92 91 0\n101 57 0 100 89 0\n102 58 0 100 90 0\n103 54 0 101 86 0\n104 55 0 102 87 0\n105 56 0 102 88 0\n106 -12 -11 0 103 21 19 17 23 25 26 29 83 0\n107 -16 -61 0 37 40 43 46 49 93 0\n108 -17 -61 0 38 41 44 47 50 93 0\n109 -10 0 105 3 7 85 0\n110 -12 0 105 9 106 85 0\n111 -14 0 105 5 11 85 0\n112 -18 0 105 14 15 85 0\n113 -9 0 105 2 6 85 0\n114 -13 0 105 4 10 85 0\n115 -61 0 111 110 112 113 109 104 114 107 108 84 36 39 42 45 48 93 0\n116 -35 0 115 94 0\n117 -36 0 115 95 0\n118 -37 0 115 96 0\n119 -38 0 115 97 0\n120 -49 0 116 79 0\n121 -50 0 117 80 0\n122 -51 0 118 81 0\n123 -52 0 119 82 0\n124 -8 0 105 103 1 16 18 20 22 24 28 85 83 27 0\n125 11 -16 0 105 121 120 117 116 109 113 124 53 32 12 85 30 35 51 56 58 59 66 65 70 69 63 64 68 67 98 0\n126 -16 0 123 122 119 118 110 114 111 12 32 53 125 8 31 34 52 55 57 61 71 75 74 72 73 78 76 77 99 0\n127 17 0 126 104 109 113 112 110 114 124 111 84 0\n128 -7 0 127 13 0\n129 -33 0 127 33 0\n130 -47 0 127 54 0\n131 -11 0 127 123 122 130 119 118 129 110 114 111 128 8 31 34 52 55 57 62 71 75 74 72 73 78 76 77 99 0\n132 15 0 131 105 85 0\n133 -29 0 132 30 0\n134 -34 0 132 35 0\n135 -43 0 132 51 0\n136 -48 0 132 56 0\n137 -53 0 132 58 0\n138 -1 0 132 127 60 0\n139 -28 0 134 138 128 124 113 129 131 116 66 0\n140 -27 0 134 138 128 124 109 129 131 117 65 0\n141 -42 0 136 138 128 124 113 130 131 120 70 0\n142 -41 0 136 138 128 124 109 130 131 121 69 0\n143 -3 0 138 124 128 113 109 131 129 134 116 117 63 0\n144 -26 0 138 124 113 109 131 116 117 64 0\n145 -40 0 138 124 113 109 131 120 121 68 0\n146 -5 0 138 124 128 113 109 131 130 136 120 121 67 0\n147 0 140 139 138 143 146 128 124 113 109 144 131 133 129 134 116 117 145 142 141 135 130 136 120 121 137 98 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record006
