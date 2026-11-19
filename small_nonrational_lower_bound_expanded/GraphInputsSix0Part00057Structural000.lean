module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsSix0Part00057Frames
public import GraphInputsSix0Part00057Leaves
public import GraphInputsSix0Part00057Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00057.record059
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f0f53d2f47c6f17b8ed9b56b9ad6b39ae6796e576799b65d7356d572f2d29c96aa6966a592e4789eb46713c5c95a4e9a64b971565396952d58d4b4ad47743b0e6358e9394cd38cc73a2d4b32d2b1ae1b46c9ba1d4731d2719e1745c9723c9c0f03a0d90e0b81eb069126439254354348d0b41d90d4318e130cd0b0ac1b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9249249249249249136db6924db6d26da49249249349a69249a692491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3, 4]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00057.record059" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00057.record059" 44

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00057.record059" "{\"ridges\":[[9,67],[10,67],[11,67],[21,193],[21,577],[33,67],[35,198],[36,67],[41,67],[43,202],[44,67],[48,67],[48,193],[49,578],[51,322],[53,704],[61,228],[62,97],[63,452],[66,232],[67,97],[68,456],[69,240],[71,704],[76,98],[78,98],[80,210],[84,98],[88,578],[89,578],[95,704],[96,704],[97,578],[102,578],[103,704]],\"owners\":[[62,97,[9,41,46,52,66,69,70,91,97],[33,51,61,67,84,90]],[67,97,[9,33,46,52,61,69,70,90,97],[41,51,62,66,84,91]],[76,98,[9,41,46,52,79,91,97],[33,51,78,84,90]],[78,98,[9,33,46,52,79,90,97],[41,51,76,84,91]],[84,98,[],[9,33,41,46,51,52,76,78,79,90,91,97]],[51,322,[],[10,36,44,54,76,78,82,83,84,100,101,102,103]],[21,577,[11,49,52,54,70,88,89,90,91,100,101,102],[71,95,96]],[49,578,[],[11,52,53,54,79,80,88,89,90,91,97,100,101,102,103]],[88,578,[],[11,49,52,53,54,79,80,89,90,91,97,100,101,102,103]],[89,578,[],[11,49,52,53,54,79,80,88,90,91,97,100,101,102,103]],[97,578,[],[11,49,52,53,54,79,80,88,89,90,91,100,101,102,103]],[102,578,[],[11,49,52,53,54,79,80,88,89,90,91,97,100,101,103]],[21,193,[35,43,48,61,63,66,68,69],[53,71,95,96,97,103]],[48,193,[21,61,63,66,68],[35,43,53,69,71,95,96,97,103]],[53,704,[],[21,71,80,95,96,97,103]],[71,704,[],[21,53,80,95,96,97,103]],[95,704,[],[21,53,71,80,96,97,103]],[96,704,[],[21,53,71,80,95,97,103]],[103,704,[],[21,53,71,80,95,96,97]],[35,198,[],[]],[43,202,[],[]],[80,210,[48],[]],[61,228,[],[]],[63,452,[],[]],[66,232,[],[]],[68,456,[],[]],[69,240,[],[]]],\"edges\":[[39,[21,35,43,48,53,61,63,66,68,69,71,80,95,96,97,103]],[40,[10,36,44,51,54,62,63,67,68,76,78,82,83,84,100,101,102,103]]],\"groupings\":[]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00057.record059" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00057.record059\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-11],[-15,-12],[-17,-12],[-25,-12],[-29,-12],[-31,-12],[-32,-12],[-36,-12],[-37,-12],[-41,-12],[-42,-12],[-1,-3,-12],[-2,-3,-12],[-3,-5,-12],[-3,-7,-12],[-3,-8,-12],[-3,-10,-12],[-19,1,8,11,15,21,24,25,37,40],[-22,1,5,11,15,18,24,25,36,40],[-27,1,8,11,15,29,37,40],[-28,1,5,11,15,29,36,40],[-33],[-14],[-4,3,13,15,17,25,34,35,36,37,41,42,43],[-13],[-34],[-35],[-40],[-43],[-4,6,9,12,18,20,21,23,24],[-12,4,18,20,21,23],[-16],[-26],[-38],[-39],[-44],[-6],[-9],[-30,12],[-18],[-20],[-21],[-23],[-24],[4,6,9,12,16,18,20,21,23,24,26,30,38,39,40,44],[2,7,10,14,17,19,20,22,23,27,28,31,32,33,41,42,43,44]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":48},{\"tag\":\"incompatible\",\"a\":70,\"b\":48},{\"tag\":\"incompatible\",\"a\":79,\"b\":48},{\"tag\":\"incompatible\",\"a\":82,\"b\":48},{\"tag\":\"incompatible\",\"a\":83,\"b\":48},{\"tag\":\"incompatible\",\"a\":90,\"b\":48},{\"tag\":\"incompatible\",\"a\":91,\"b\":48},{\"tag\":\"incompatible\",\"a\":100,\"b\":48},{\"tag\":\"incompatible\",\"a\":101,\"b\":48},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[9,11,48]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[10,11,48]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[11,33,48]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[11,36,48]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[11,41,48]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[11,44,48]},{\"tag\":\"mate\",\"ridge\":97,\"a\":62,\"owners\":[9,41,46,52,66,69,70,91,97]},{\"tag\":\"mate\",\"ridge\":97,\"a\":67,\"owners\":[9,33,46,52,61,69,70,90,97]},{\"tag\":\"mate\",\"ridge\":98,\"a\":76,\"owners\":[9,41,46,52,79,91,97]},{\"tag\":\"mate\",\"ridge\":98,\"a\":78,\"owners\":[9,33,46,52,79,90,97]},{\"tag\":\"mate\",\"ridge\":98,\"a\":84,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":322,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":577,\"a\":21,\"owners\":[11,49,52,54,70,88,89,90,91,100,101,102]},{\"tag\":\"mate\",\"ridge\":578,\"a\":49,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":578,\"a\":88,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":578,\"a\":89,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":578,\"a\":97,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":578,\"a\":102,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":193,\"a\":21,\"owners\":[35,43,48,61,63,66,68,69]},{\"tag\":\"mate\",\"ridge\":193,\"a\":48,\"owners\":[21,61,63,66,68]},{\"tag\":\"mate\",\"ridge\":704,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":704,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":704,\"a\":95,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":704,\"a\":96,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":704,\"a\":103,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":198,\"a\":35,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":202,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":210,\"a\":80,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":228,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":452,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":232,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":240,\"a\":69,\"owners\":[]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[21,35,43,48,53,61,63,66,68,69,71,80,95,96,97,103]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[10,36,44,51,54,62,63,67,68,76,78,82,83,84,100,101,102,103]}]}"
  "47 4 12 30 0 37 38 32 40 41 42 43 44 33 34 35 28 36 45 0\n48 2 7 10 17 19 22 27 28 31 32 41 42 0 23 41 43 22 29 36 46 0\n49 12 0 44 43 42 41 40 38 37 30 39 47 0\n50 -11 0 49 1 0\n51 -15 0 49 2 0\n52 -17 0 49 3 0\n53 -25 0 49 4 0\n54 -29 0 49 5 0\n55 -36 0 49 8 0\n56 -37 0 49 9 0\n57 -41 0 49 10 0\n58 -42 0 49 11 0\n59 4 0 49 40 41 42 43 31 0\n60 3 0 59 25 51 52 53 26 27 55 56 57 58 29 24 0\n61 -31 0 49 6 0\n62 -32 0 49 7 0\n63 -1 0 60 49 12 0\n64 -2 0 60 49 13 0\n65 -5 0 60 49 14 0\n66 -7 0 60 49 15 0\n67 -8 0 60 49 16 0\n68 -10 0 60 49 17 0\n69 -28 0 63 65 50 51 54 55 28 21 0\n70 -19 0 63 67 50 51 42 44 53 56 28 18 0\n71 -27 0 63 67 50 51 54 56 28 20 0\n72 22 0 64 66 52 68 70 71 69 61 62 57 58 48 0\n73 0 65 72 63 50 51 40 44 53 55 28 19 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_certificates, Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059 Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_validity Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00057.record059
