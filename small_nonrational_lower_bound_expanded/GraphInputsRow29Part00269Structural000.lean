module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00269Frames
public import GraphInputsRow29Part00269Leaves
public import GraphInputsRow29Part00269Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "cd32c9b16c3b31c372b2aaa6a3aa9a36a66398d68d9362da4e33a2e4b8ae1b91e2785e6c5a95a4e9664d9594e5356354d4b5534cd8b52d2b46d8749d174d38cd332ce2b4acab1ae1b46c5b31e2749ca785d1725c570de0f43c8f0be1c470e232a1a26a2619a168384e078e13251926525195154344d074c328c6324c8b12c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6da6db4924d36926d249b69249b4d269a4926d3692492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 61), (facetIndex 66), (facetIndex 69)]))
 (.branch 2
 (.leaf ([(facetIndex 82), (facetIndex 87), (facetIndex 90)]))
 (.leaf ([(facetIndex 99), (facetIndex 101)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 77), (facetIndex 98), (facetIndex 105)]))
 (.leaf ([(facetIndex 68), (facetIndex 88)])))
 (.branch 6
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 75), (facetIndex 76), (facetIndex 96), (facetIndex 97), (facetIndex 104)]))
 (.leaf ([(facetIndex 63), (facetIndex 83), (facetIndex 102), (facetIndex 103)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1dd904ed000044200c4001da00004000c000006c5az26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [3]
def grouped3_0003 : List Nat := [3, 4]
def grouped3_0004 : List Nat := [3, 4, 5, 6]
def grouped3_0005 : List Nat := [4]
def grouped3_0006 : List Nat := [5]
def grouped3_0007 : List Nat := [5, 6]
def grouped3_0008 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0003\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record002" 36

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record002" "{\"ridges\":[[16,289],[16,292],[26,546],[43,289],[44,546],[51,298],[52,553],[54,306],[62,292],[63,553],[67,289],[71,289],[71,292],[75,360],[76,424],[77,432],[83,298],[84,546],[84,548],[89,546],[92,546],[96,616],[97,680],[98,688],[102,360],[103,616],[104,808],[105,816]],\"owners\":[[16,289,[51,54,75,76,77],[43,62,67,71]],[43,289,[75,76,77],[16,51,54,62,67,71]],[67,289,[51,75,76],[16,43,54,62,71,77]],[71,289,[51,54,76,77],[16,43,62,67,75]],[16,292,[83,88,102,104,105],[43,62,67,71]],[62,292,[88,105],[16,43,67,71,83,102,104]],[71,292,[83,88,104,105],[16,43,62,67,102]],[26,546,[52,55,96,97,98],[44,84,89,92]],[44,546,[96,97,98],[26,52,55,84,89,92]],[84,546,[55,98],[26,44,52,89,92,96,97]],[89,546,[52,96,97],[26,44,55,84,92,98]],[92,546,[52,55,97,98],[26,44,84,89,96]],[84,548,[68,105],[26,44,63,89,92,103,104]],[51,298,[83],[]],[83,298,[51],[]],[52,553,[63],[]],[63,553,[52],[]],[54,306,[88],[]],[75,360,[102],[]],[102,360,[75],[]],[76,424,[],[]],[77,432,[],[]],[96,616,[103],[]],[103,616,[96],[]],[97,680,[],[]],[98,688,[],[]],[104,808,[],[]],[105,816,[],[]]],\"edges\":[[37,[16,43,51,54,62,67,71,75,76,77,83,88,102,104,105]],[38,[26,44,52,55,63,68,84,89,92,96,97,98,103,104,105]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-5],[-14,-6],[-17,-6],[-19,-8],[-19,-12],[-21,-19],[-22,-5],[-22,-14],[-22,-17],[-25,-22],[-1,5,7,14,15,16],[-3,14,15,16],[-11,5,14,15],[-13,5,7,15,16],[-1,17,19,25,27,28],[-9,19,28],[-13,17,19,27,28],[-2,6,8,22,23,24],[-4,22,23,24],[-18,8,24],[-20,6,22,23],[-21,6,8,23,24],[-18,12,28],[-5,17],[-17,5],[-6,10],[-10,6],[-7,19],[-14,25],[-25,14],[-15],[-16],[-22,26],[-26,22],[-23],[-24],[-27],[-28],[-7,29],[-8,29],[-12,30],[-19,30],[-5,31],[-6,31],[-14,31],[-22,31],[-10,32],[-17,32],[-25,32],[-26,32],[-30,33],[-29,33],[-31,-32,34],[-33,-34,35],[-35,36],[-36],[1,3,5,7,9,11,13,14,15,16,17,19,25,27,28],[2,4,6,8,10,12,18,20,21,22,23,24,26,27,28]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":75,\"b\":52},{\"tag\":\"incompatible\",\"a\":83,\"b\":52},{\"tag\":\"incompatible\",\"a\":88,\"b\":55},{\"tag\":\"incompatible\",\"a\":88,\"b\":68},{\"tag\":\"incompatible\",\"a\":92,\"b\":88},{\"tag\":\"incompatible\",\"a\":96,\"b\":51},{\"tag\":\"incompatible\",\"a\":96,\"b\":75},{\"tag\":\"incompatible\",\"a\":96,\"b\":83},{\"tag\":\"incompatible\",\"a\":102,\"b\":96},{\"tag\":\"mate\",\"ridge\":289,\"a\":16,\"owners\":[51,54,75,76,77]},{\"tag\":\"mate\",\"ridge\":289,\"a\":43,\"owners\":[75,76,77]},{\"tag\":\"mate\",\"ridge\":289,\"a\":67,\"owners\":[51,75,76]},{\"tag\":\"mate\",\"ridge\":289,\"a\":71,\"owners\":[51,54,76,77]},{\"tag\":\"mate\",\"ridge\":292,\"a\":16,\"owners\":[83,88,102,104,105]},{\"tag\":\"mate\",\"ridge\":292,\"a\":62,\"owners\":[88,105]},{\"tag\":\"mate\",\"ridge\":292,\"a\":71,\"owners\":[83,88,104,105]},{\"tag\":\"mate\",\"ridge\":546,\"a\":26,\"owners\":[52,55,96,97,98]},{\"tag\":\"mate\",\"ridge\":546,\"a\":44,\"owners\":[96,97,98]},{\"tag\":\"mate\",\"ridge\":546,\"a\":84,\"owners\":[55,98]},{\"tag\":\"mate\",\"ridge\":546,\"a\":89,\"owners\":[52,96,97]},{\"tag\":\"mate\",\"ridge\":546,\"a\":92,\"owners\":[52,55,97,98]},{\"tag\":\"mate\",\"ridge\":548,\"a\":84,\"owners\":[68,105]},{\"tag\":\"mate\",\"ridge\":298,\"a\":51,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":298,\"a\":83,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":553,\"a\":52,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":553,\"a\":63,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":306,\"a\":54,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":360,\"a\":75,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":360,\"a\":102,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":424,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":616,\"a\":96,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":616,\"a\":103,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":680,\"a\":97,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":98,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":808,\"a\":104,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":105,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":54,\"full_literals\":[-7,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":55,\"full_literals\":[-8,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-12,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-19,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":51,\"full_literals\":[-5,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-6,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-14,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":96,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-10,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-17,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":102,\"full_literals\":[-25,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":103,\"full_literals\":[-26,32]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-32,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-33,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[16,43,51,54,62,67,71,75,76,77,83,88,102,104,105]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[26,44,52,55,63,68,84,89,92,96,97,98,103,104,105]}]}"
  "59 -35 0 56 55 0\n60 1 3 5 7 9 11 13 14 17 19 25 0 31 32 37 38 57 0\n61 2 4 6 8 10 12 18 20 21 22 26 0 35 36 37 38 58 0\n62 6 22 33 0 38 36 35 34 19 51 41 23 52 40 27 22 18 21 61 0\n63 14 -6 33 0 38 32 31 52 39 1 14 3 51 42 16 12 30 11 13 60 0\n64 -6 33 0 63 2 0\n65 33 0 38 32 31 51 52 42 39 16 64 62 7 8 9 10 14 11 13 12 60 0\n66 -34 0 65 59 54 0\n67 -22 0 66 33 46 50 53 0\n68 -4 0 67 35 36 19 0\n69 -26 0 67 34 0\n70 19 5 14 0 32 31 38 37 13 25 30 12 16 28 17 15 60 0\n71 -19 6 0 36 35 69 67 68 21 27 4 5 6 20 18 61 0\n72 -5 0 66 24 43 48 53 0\n73 -14 0 66 29 45 49 53 0\n74 19 0 73 72 70 0\n75 6 0 74 71 0\n76 10 0 75 26 0\n77 31 0 75 44 0\n78 32 0 76 47 0\n79 0 77 78 66 53 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ad26c371b25a8da35a364d8b633a2e4b86e8791e2785ecc6b16c7299a569c64d9a9665a54d58d5352d64d3362d4b46d4749d175a358d9334e334ccb352ccb8ad2b1ae1b26c5b89d2785d1715c3783d0f23c2f3921c3891a318a6198961381e38619464c5894a5196152560d1341d30d2328c6344c9342c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db4da4da4926db6d34924d249a492493492692492492492249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 76)]))
 (.branch 2
 (.leaf ([(facetIndex 96)]))
 (.leaf ([(facetIndex 99)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 51), (facetIndex 65), (facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 56), (facetIndex 70), (facetIndex 81), (facetIndex 82), (facetIndex 83)])))
 (.branch 6
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 97), (facetIndex 100)]))
 (.leaf ([(facetIndex 93), (facetIndex 94), (facetIndex 98), (facetIndex 101)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "355a91b01680009236c00001000180000040006z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [3]
def grouped3_0003 : List Nat := [3, 4]
def grouped3_0004 : List Nat := [3, 4, 5, 6]
def grouped3_0005 : List Nat := [4]
def grouped3_0006 : List Nat := [5]
def grouped3_0007 : List Nat := [5, 6]
def grouped3_0008 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0003\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record003" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record003" "{\"ridges\":[[12,289],[21,545],[44,289],[45,545],[50,289],[50,290],[51,554],[55,289],[55,290],[56,562],[59,289],[60,289],[65,300],[66,545],[66,548],[70,308],[71,545],[71,548],[74,545],[75,545],[78,360],[79,616],[80,808],[81,432],[82,688],[83,816],[89,300],[93,308],[94,562],[97,360],[98,432],[101,688]],\"owners\":[[12,289,[65,70,78,80,81,83],[44,50,55,59,60]],[44,289,[78,80,81,83],[12,50,55,59,60,65,70]],[50,289,[70,81,83],[12,44,55,59,60,65,78,80]],[55,289,[65,78,80],[12,44,50,59,60,70,81,83]],[59,289,[65,70,80,81,83],[12,44,50,55,60,78]],[60,289,[65,70,78,80,83],[12,44,50,55,59,81]],[50,290,[93,98],[12,44,55,59,60,89,97]],[55,290,[89,97],[12,44,50,59,60,93,98]],[21,545,[51,56,79,80,82,83],[45,66,71,74,75]],[45,545,[79,80,82,83],[21,51,56,66,71,74,75]],[66,545,[56,82,83],[21,45,51,71,74,75,79,80]],[71,545,[51,79,80],[21,45,56,66,74,75,82,83]],[74,545,[51,56,80,82,83],[21,45,66,71,75,79]],[75,545,[51,56,79,80,83],[21,45,66,71,74,82]],[66,548,[94,101],[21,45,71,74,75,90,100]],[71,548,[90,100],[21,45,66,74,75,94,101]],[51,554,[90],[]],[56,562,[94],[]],[94,562,[56],[]],[65,300,[89],[]],[89,300,[65],[]],[70,308,[93],[]],[93,308,[70],[]],[78,360,[97],[]],[97,360,[78],[]],[79,616,[100],[]],[80,808,[],[]],[81,432,[98],[]],[98,432,[81],[]],[82,688,[101],[]],[101,688,[82],[]],[83,816,[],[]]],\"edges\":[[37,[12,44,50,55,59,60,65,70,78,80,81,83,89,93,97,98]],[38,[21,45,51,56,66,71,74,75,79,80,82,83,90,94,100,101]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-4,-3],[-9,-4],[-9,-8],[-10,-4],[-10,-8],[-11,-4],[-11,-6],[-13,-4],[-13,-8],[-15,-3],[-15,-11],[-15,-13],[-16,-3],[-16,-11],[-16,-13],[-17,-6],[-18,-11],[-18,-17],[-20,-8],[-21,-13],[-21,-20],[-24,-11],[-24,-17],[-25,-8],[-25,-21],[-26,-20],[-28,-8],[-28,-21],[-29,-11],[-29,-17],[-30,-20],[-1,11,13,17,19,20,22],[-3,17,19,20,22],[-5,13,20,22],[-7,11,17,19],[-9,11,13,19,20,22],[-10,11,13,17,19,22],[-5,25,28],[-7,23,27],[-2,6,8,18,19,21,22],[-4,18,19,21,22],[-12,8,21,22],[-14,6,18,19],[-15,6,8,19,21,22],[-16,6,8,18,19,22],[-12,26,30],[-14,24,29],[-6,24],[-8,26],[-26,8],[-11,23],[-23,11],[-13,25],[-25,13],[-17,27],[-27,17],[-18,29],[-19],[-20,28],[-28,20],[-21,30],[-30,21],[-22],[-8,31],[-13,31],[-20,31],[-21,31],[-23,32],[-24,32],[-27,32],[-29,32],[-33,25,26,28,30],[-25,33],[-26,33],[-28,33],[-30,33],[-31,34],[-35,33],[-32,-33,35],[-34,-35,36],[-36,37],[-37],[1,3,5,7,9,10,11,13,17,19,20,22,23,25,27,28],[2,4,6,8,12,14,15,16,18,19,21,22,24,26,29,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":59,\"b\":45},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":45},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":70,\"b\":45},{\"tag\":\"incompatible\",\"a\":70,\"b\":56},{\"tag\":\"incompatible\",\"a\":74,\"b\":44},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":44},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":51},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":56},{\"tag\":\"incompatible\",\"a\":82,\"b\":70},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":90,\"b\":65},{\"tag\":\"incompatible\",\"a\":90,\"b\":78},{\"tag\":\"incompatible\",\"a\":93,\"b\":56},{\"tag\":\"incompatible\",\"a\":93,\"b\":82},{\"tag\":\"incompatible\",\"a\":94,\"b\":81},{\"tag\":\"incompatible\",\"a\":98,\"b\":56},{\"tag\":\"incompatible\",\"a\":98,\"b\":82},{\"tag\":\"incompatible\",\"a\":100,\"b\":65},{\"tag\":\"incompatible\",\"a\":100,\"b\":78},{\"tag\":\"incompatible\",\"a\":101,\"b\":81},{\"tag\":\"mate\",\"ridge\":289,\"a\":12,\"owners\":[65,70,78,80,81,83]},{\"tag\":\"mate\",\"ridge\":289,\"a\":44,\"owners\":[78,80,81,83]},{\"tag\":\"mate\",\"ridge\":289,\"a\":50,\"owners\":[70,81,83]},{\"tag\":\"mate\",\"ridge\":289,\"a\":55,\"owners\":[65,78,80]},{\"tag\":\"mate\",\"ridge\":289,\"a\":59,\"owners\":[65,70,80,81,83]},{\"tag\":\"mate\",\"ridge\":289,\"a\":60,\"owners\":[65,70,78,80,83]},{\"tag\":\"mate\",\"ridge\":290,\"a\":50,\"owners\":[93,98]},{\"tag\":\"mate\",\"ridge\":290,\"a\":55,\"owners\":[89,97]},{\"tag\":\"mate\",\"ridge\":545,\"a\":21,\"owners\":[51,56,79,80,82,83]},{\"tag\":\"mate\",\"ridge\":545,\"a\":45,\"owners\":[79,80,82,83]},{\"tag\":\"mate\",\"ridge\":545,\"a\":66,\"owners\":[56,82,83]},{\"tag\":\"mate\",\"ridge\":545,\"a\":71,\"owners\":[51,79,80]},{\"tag\":\"mate\",\"ridge\":545,\"a\":74,\"owners\":[51,56,80,82,83]},{\"tag\":\"mate\",\"ridge\":545,\"a\":75,\"owners\":[51,56,79,80,83]},{\"tag\":\"mate\",\"ridge\":548,\"a\":66,\"owners\":[94,101]},{\"tag\":\"mate\",\"ridge\":548,\"a\":71,\"owners\":[90,100]},{\"tag\":\"mate\",\"ridge\":554,\"a\":51,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":562,\"a\":56,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":562,\"a\":94,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":300,\"a\":65,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":300,\"a\":89,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":308,\"a\":70,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":308,\"a\":93,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":360,\"a\":78,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":360,\"a\":97,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":616,\"a\":79,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":808,\"a\":80,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":81,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":432,\"a\":98,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":688,\"a\":82,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":688,\"a\":101,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":816,\"a\":83,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":56,\"full_literals\":[-8,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-13,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-20,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-21,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":89,\"full_literals\":[-23,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":90,\"full_literals\":[-24,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":97,\"full_literals\":[-27,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":100,\"full_literals\":[-29,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[93,94,98,101],\"full_literals\":[-33,25,26,28,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-25,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-26,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":98,\"full_literals\":[-28,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":101,\"full_literals\":[-30,33]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[12,44,50,55,59,60,65,70,78,80,81,83,89,93,97,98]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[21,45,51,56,66,71,74,75,79,80,82,83,90,94,100,101]}]}"
  "85 -36 0 82 81 0\n86 1 3 5 7 9 10 11 13 17 20 23 25 27 28 0 58 63 83 0\n87 2 4 6 8 12 14 15 16 18 21 24 26 29 30 0 58 63 84 0\n88 -35 0 85 78 80 77 64 65 66 67 50 54 60 62 72 0\n89 -4 5 32 0 63 58 71 57 70 55 68 51 39 1 2 4 8 41 54 21 28 32 86 0\n90 -16 32 0 63 58 71 57 70 55 69 48 68 51 39 13 15 45 54 37 3 19 27 38 32 86 0\n91 -4 32 0 58 63 71 57 8 41 89 21 34 0\n92 20 -15 32 0 58 63 68 51 70 55 12 37 54 10 39 60 32 36 34 86 0\n93 -15 32 0 63 58 69 48 92 19 21 44 0\n94 -20 32 0 63 58 93 91 90 69 71 47 57 48 19 21 26 31 42 40 87 0\n95 8 21 32 0 63 58 62 93 91 90 69 71 47 57 48 50 42 40 87 0\n96 -8 32 0 58 63 70 55 94 33 60 68 51 39 3 5 9 24 32 34 86 0\n97 32 0 58 63 68 70 39 51 55 94 60 33 96 95 20 25 37 32 36 34 86 0\n98 -33 0 97 88 79 0\n99 -25 0 98 73 0\n100 -26 0 98 74 0\n101 -28 0 98 75 0\n102 -30 0 98 76 0\n103 -13 0 99 53 0\n104 -5 0 99 101 38 0\n105 -8 0 100 49 0\n106 -20 0 101 59 0\n107 -21 0 102 61 0\n108 -12 0 102 100 46 0\n109 11 10 17 0 63 58 101 106 99 104 103 33 56 35 52 32 36 86 0\n110 -11 0 63 58 100 108 102 105 107 6 7 11 14 17 22 29 40 43 87 0\n111 17 0 63 58 103 110 37 109 0\n112 -6 0 111 16 0\n113 -18 0 111 18 0\n114 -24 0 111 23 0\n115 -29 0 111 30 0\n116 -15 0 112 105 58 107 63 44 0\n117 -2 0 112 105 107 58 113 63 40 0\n118 -14 0 113 112 58 43 0\n119 -16 0 113 105 112 58 63 45 0\n120 -4 0 113 58 107 63 41 0\n121 0 113 118 120 107 112 119 105 102 108 116 114 100 115 117 87 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00269.record003
