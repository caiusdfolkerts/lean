module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00239Frames
public import GraphInputsRow29Part00239Leaves
public import GraphInputsRow29Part00239Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00239.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9e2748f0bc9a96a568ba1ea66599562d87663a2e4b8ae47a71d26695a659566392e479d166559655556352d475c368d6352d2b61d4766358d5334cb362e4b52e2b4acab1ad1b16d8791d4789d2729c6745c5783e2c2703c1c89a0e8960d90e2382e07a611c62926439894950d60d4348d0b41d50c6324c530cd0b22c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b49b6936d249249a6da49a6da492492492493492492692492449249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 77)]))
 (.leaf ([(facetIndex 56), (facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 96), (facetIndex 104)]))
 (.leaf ([(facetIndex 99), (facetIndex 100), (facetIndex 101), (facetIndex 105)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "e0fc2a0000454000000000001z1c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [2]
def grouped3_0005 : List Nat := [2, 3]
def grouped3_0006 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00239.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00239.record002" 35

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00239.record002" "{\"ridges\":[[13,321],[13,322],[26,577],[46,321],[46,322],[47,582],[55,322],[56,586],[60,321],[60,322],[61,321],[61,322],[62,577],[73,340],[74,596],[75,356],[76,577],[76,608],[77,836],[81,344],[82,600],[83,360],[84,577],[84,608],[85,840],[86,577],[96,582],[99,344],[100,360],[101,586],[104,596],[105,600]],\"owners\":[[13,321,[73,75,77,81,83,85],[46,55,60,61]],[46,321,[81,83,85],[13,55,60,61,73,75,77]],[60,321,[75,77,83,85],[13,46,55,61,73,81]],[61,321,[73,77,81,85],[13,46,55,60,75,83]],[13,322,[94,95,99,100],[46,55,60,61]],[46,322,[99,100],[13,55,60,61,94,95]],[55,322,[94,95],[13,46,60,61,99,100]],[60,322,[95,100],[13,46,55,61,94,99]],[61,322,[94,99],[13,46,55,60,95,100]],[26,577,[47,56,74,77,82,85],[62,76,84,86]],[62,577,[74,77,82,85],[26,47,56,76,84,86]],[76,577,[56,82,85],[26,47,62,74,77,84,86]],[84,577,[47,74,77],[26,56,62,76,82,85,86]],[86,577,[47,56,77,85],[26,62,74,76,82,84]],[76,608,[101,105],[26,62,84,86,96,104]],[84,608,[96,104],[26,62,76,86,101,105]],[47,582,[96],[]],[96,582,[47],[]],[56,586,[101],[]],[101,586,[56],[]],[73,340,[94],[]],[74,596,[104],[]],[104,596,[74],[]],[75,356,[95],[]],[77,836,[],[]],[81,344,[99],[]],[99,344,[81],[]],[82,600,[105],[]],[105,600,[82],[]],[83,360,[100],[]],[100,360,[83],[]],[85,840,[],[]]],\"edges\":[[40,[13,46,55,60,61,73,75,77,81,83,85,94,95,99,100]],[41,[26,47,56,62,74,76,77,82,84,85,86,96,101,104,105]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00239.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00239.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-6],[-16,-15],[-17,-6],[-17,-16],[-20,-17],[-21,-4],[-21,-11],[-22,-4],[-22,-11],[-23,-21],[-23,-22],[-26,-15],[-26,-17],[-27,-21],[-27,-22],[-28,-15],[-1,10,12,14,15,17,19],[-3,15,17,19],[-7,12,14,17,19],[-8,10,14,15,19],[-1,21,22,24,25],[-3,24,25],[-5,21,22],[-7,22,25],[-8,21,24],[-2,4,6,11,14,16,19],[-9,11,14,16,19],[-13,6,16,19],[-18,4,11,14],[-20,4,6,14,19],[-13,26,28],[-18,23,27],[-4,23],[-23,4],[-6,26],[-26,6],[-10,21],[-11,27],[-27,11],[-12,22],[-14],[-15,24],[-24,15],[-16,28],[-28,16],[-17,25],[-25,17],[-19],[-4,29],[-11,29],[-6,30],[-16,30],[-21,31],[-22,31],[-23,31],[-27,31],[-24,32],[-25,32],[-26,32],[-28,32],[-30,33],[-29,33],[-31,-32,34],[-33,-34,35],[-35],[1,3,5,7,8,10,12,14,15,17,19,21,22,24,25],[2,4,6,9,11,13,14,16,18,19,20,23,26,27,28]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":81,\"b\":56},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":56},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":94,\"b\":47},{\"tag\":\"incompatible\",\"a\":94,\"b\":74},{\"tag\":\"incompatible\",\"a\":95,\"b\":47},{\"tag\":\"incompatible\",\"a\":95,\"b\":74},{\"tag\":\"incompatible\",\"a\":96,\"b\":94},{\"tag\":\"incompatible\",\"a\":96,\"b\":95},{\"tag\":\"incompatible\",\"a\":101,\"b\":81},{\"tag\":\"incompatible\",\"a\":101,\"b\":83},{\"tag\":\"incompatible\",\"a\":104,\"b\":94},{\"tag\":\"incompatible\",\"a\":104,\"b\":95},{\"tag\":\"incompatible\",\"a\":105,\"b\":81},{\"tag\":\"mate\",\"ridge\":321,\"a\":13,\"owners\":[73,75,77,81,83,85]},{\"tag\":\"mate\",\"ridge\":321,\"a\":46,\"owners\":[81,83,85]},{\"tag\":\"mate\",\"ridge\":321,\"a\":60,\"owners\":[75,77,83,85]},{\"tag\":\"mate\",\"ridge\":321,\"a\":61,\"owners\":[73,77,81,85]},{\"tag\":\"mate\",\"ridge\":322,\"a\":13,\"owners\":[94,95,99,100]},{\"tag\":\"mate\",\"ridge\":322,\"a\":46,\"owners\":[99,100]},{\"tag\":\"mate\",\"ridge\":322,\"a\":55,\"owners\":[94,95]},{\"tag\":\"mate\",\"ridge\":322,\"a\":60,\"owners\":[95,100]},{\"tag\":\"mate\",\"ridge\":322,\"a\":61,\"owners\":[94,99]},{\"tag\":\"mate\",\"ridge\":577,\"a\":26,\"owners\":[47,56,74,77,82,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":62,\"owners\":[74,77,82,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":76,\"owners\":[56,82,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":84,\"owners\":[47,74,77]},{\"tag\":\"mate\",\"ridge\":577,\"a\":86,\"owners\":[47,56,77,85]},{\"tag\":\"mate\",\"ridge\":608,\"a\":76,\"owners\":[101,105]},{\"tag\":\"mate\",\"ridge\":608,\"a\":84,\"owners\":[96,104]},{\"tag\":\"mate\",\"ridge\":582,\"a\":47,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":582,\"a\":96,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":586,\"a\":56,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":586,\"a\":101,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":340,\"a\":73,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":596,\"a\":74,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":596,\"a\":104,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":356,\"a\":75,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":836,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":344,\"a\":81,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":344,\"a\":99,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":600,\"a\":82,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":600,\"a\":105,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":360,\"a\":83,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":360,\"a\":100,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":840,\"a\":85,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":47,\"full_literals\":[-4,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-11,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":56,\"full_literals\":[-6,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-16,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":94,\"full_literals\":[-21,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":95,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":96,\"full_literals\":[-23,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":104,\"full_literals\":[-27,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":99,\"full_literals\":[-24,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":100,\"full_literals\":[-25,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":101,\"full_literals\":[-26,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":105,\"full_literals\":[-28,32]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0003\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0003\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-32,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-33,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[13,46,55,60,61,73,75,77,81,83,85,94,95,99,100]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[26,47,56,62,74,76,77,82,84,85,86,96,101,104,105]}]}"
  "68 1 3 5 7 8 10 12 15 17 21 22 24 25 0 41 48 66 0\n69 2 4 6 9 11 13 16 18 20 23 26 27 28 0 41 48 67 0\n70 33 0 48 41 61 62 51 52 49 50 36 30 45 28 34 27 39 29 26 69 0\n71 -34 0 70 65 64 0\n72 -17 16 31 0 41 48 56 38 27 45 55 32 33 3 5 13 26 28 69 0\n73 17 15 31 0 48 41 53 37 20 43 54 23 40 47 19 18 17 68 0\n74 -17 31 0 4 72 0\n75 31 0 48 41 55 56 33 38 32 74 73 1 2 12 16 30 26 28 27 69 0\n76 -32 0 75 71 63 0\n77 -24 0 76 57 0\n78 -25 0 76 58 0\n79 -26 0 76 59 0\n80 -28 0 76 60 0\n81 -15 0 77 42 0\n82 -3 0 77 78 22 0\n83 -17 0 78 46 0\n84 -6 0 79 35 0\n85 -13 0 79 80 31 0\n86 -16 0 80 44 0\n87 21 22 0 78 83 77 81 82 24 40 37 25 23 21 68 0\n88 -21 0 48 41 80 86 79 85 84 6 7 10 14 30 29 26 27 69 0\n89 22 0 88 87 0\n90 -4 0 89 8 0\n91 -11 0 89 9 0\n92 -23 0 89 11 0\n93 -27 0 89 15 0\n94 -20 0 90 84 41 48 30 0\n95 -18 0 91 90 41 29 0\n96 -2 0 91 90 84 41 86 48 26 0\n97 -9 0 91 41 86 48 27 0\n98 0 96 93 90 97 84 91 85 95 94 92 79 86 80 69 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00239.record002
