module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00021Frames
public import GraphInputsRow23Part00021Leaves
public import GraphInputsRow23Part00021Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "6e1b46b19c6c9aa5a93ac59969593663a4e5392e1b91e6c5a93a4b9a5595954b56364d334ad1b49d98e538cd332cc7392d2b2ac3b19d1725c570de0f43c8f0bc1f6c1a86518c4c92a1aa46859164384e2c4a91a645854952344d90c6384c3312c2b81c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 44), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 37), (facetIndex 57), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 61)]))
 (.branch 4
 (.leaf ([(facetIndex 34), (facetIndex 39), (facetIndex 43), (facetIndex 54), (facetIndex 68)]))
 (.leaf ([(facetIndex 38), (facetIndex 71), (facetIndex 73)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 75)]))
 (.leaf ([(facetIndex 33), (facetIndex 42), (facetIndex 46), (facetIndex 55), (facetIndex 58), (facetIndex 62), (facetIndex 63)])))
 (.branch 8
 (.leaf ([(facetIndex 30), (facetIndex 40), (facetIndex 50), (facetIndex 60), (facetIndex 64), (facetIndex 74), (facetIndex 78), (facetIndex 81)]))
 (.branch 9
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 45), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 35), (facetIndex 56), (facetIndex 70), (facetIndex 79), (facetIndex 80)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7997885748498355576627161963222700068036873410936827z1e;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_matrix_checked

def leafCount : Nat := 20
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 11), (facetIndex 23), (facetIndex 49), (facetIndex 54), (facetIndex 59), (facetIndex 61), (facetIndex 63), (facetIndex 67), (facetIndex 71), (facetIndex 72), (facetIndex 74), (facetIndex 79)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 11), (facetIndex 23), (facetIndex 49), (facetIndex 54), (facetIndex 59), (facetIndex 61), (facetIndex 63), (facetIndex 67), (facetIndex 70), (facetIndex 71), (facetIndex 76), (facetIndex 78)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 7), (facetIndex 15), (facetIndex 16), (facetIndex 27), (facetIndex 46), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 75), (facetIndex 81)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 7), (facetIndex 12), (facetIndex 15), (facetIndex 28), (facetIndex 46), (facetIndex 49), (facetIndex 53), (facetIndex 57), (facetIndex 60), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 75), (facetIndex 80)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 27), (facetIndex 46), (facetIndex 49), (facetIndex 56), (facetIndex 57), (facetIndex 61), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 75), (facetIndex 81)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 28), (facetIndex 46), (facetIndex 49), (facetIndex 50), (facetIndex 57), (facetIndex 61), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 75), (facetIndex 80)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 7), (facetIndex 14), (facetIndex 15), (facetIndex 28), (facetIndex 46), (facetIndex 49), (facetIndex 53), (facetIndex 59), (facetIndex 60), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 75), (facetIndex 80)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 11), (facetIndex 23), (facetIndex 47), (facetIndex 54), (facetIndex 59), (facetIndex 61), (facetIndex 63), (facetIndex 67), (facetIndex 71), (facetIndex 72), (facetIndex 74), (facetIndex 79)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 11), (facetIndex 23), (facetIndex 47), (facetIndex 54), (facetIndex 59), (facetIndex 61), (facetIndex 63), (facetIndex 67), (facetIndex 70), (facetIndex 71), (facetIndex 76), (facetIndex 78)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 8), (facetIndex 14), (facetIndex 15), (facetIndex 28), (facetIndex 46), (facetIndex 48), (facetIndex 53), (facetIndex 59), (facetIndex 60), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 75), (facetIndex 80)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 15), (facetIndex 19), (facetIndex 49), (facetIndex 53), (facetIndex 57), (facetIndex 58), (facetIndex 60), (facetIndex 68), (facetIndex 73), (facetIndex 75), (facetIndex 77), (facetIndex 79)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 15), (facetIndex 19), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 62), (facetIndex 68), (facetIndex 73), (facetIndex 75), (facetIndex 77), (facetIndex 78)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 7), (facetIndex 23), (facetIndex 24), (facetIndex 27), (facetIndex 45), (facetIndex 49), (facetIndex 54), (facetIndex 55), (facetIndex 59), (facetIndex 61), (facetIndex 67), (facetIndex 70), (facetIndex 71), (facetIndex 81)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 7), (facetIndex 20), (facetIndex 23), (facetIndex 28), (facetIndex 45), (facetIndex 49), (facetIndex 54), (facetIndex 55), (facetIndex 59), (facetIndex 61), (facetIndex 67), (facetIndex 71), (facetIndex 74), (facetIndex 80)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 7), (facetIndex 18), (facetIndex 19), (facetIndex 27), (facetIndex 45), (facetIndex 49), (facetIndex 54), (facetIndex 55), (facetIndex 59), (facetIndex 61), (facetIndex 70), (facetIndex 71), (facetIndex 75), (facetIndex 81)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 7), (facetIndex 18), (facetIndex 25), (facetIndex 28), (facetIndex 45), (facetIndex 49), (facetIndex 54), (facetIndex 55), (facetIndex 59), (facetIndex 61), (facetIndex 64), (facetIndex 71), (facetIndex 75), (facetIndex 80)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 7), (facetIndex 22), (facetIndex 23), (facetIndex 28), (facetIndex 45), (facetIndex 49), (facetIndex 54), (facetIndex 55), (facetIndex 59), (facetIndex 61), (facetIndex 67), (facetIndex 73), (facetIndex 74), (facetIndex 80)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 15), (facetIndex 19), (facetIndex 47), (facetIndex 53), (facetIndex 57), (facetIndex 58), (facetIndex 60), (facetIndex 68), (facetIndex 73), (facetIndex 75), (facetIndex 77), (facetIndex 79)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 15), (facetIndex 19), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 62), (facetIndex 68), (facetIndex 73), (facetIndex 75), (facetIndex 77), (facetIndex 78)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 8), (facetIndex 22), (facetIndex 23), (facetIndex 28), (facetIndex 45), (facetIndex 48), (facetIndex 54), (facetIndex 55), (facetIndex 59), (facetIndex 61), (facetIndex 67), (facetIndex 73), (facetIndex 74), (facetIndex 80)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
 (.branch 3
 (.leaf (leaf0002))
 (.branch 4
 (.leaf (leaf0003))
 (.leaf (leaf0004)))))
 (.branch 7
 (.branch 6
 (.leaf (leaf0005))
 (.leaf (leaf0006)))
 (.branch 8
 (.leaf (leaf0007))
 (.branch 9
 (.leaf (leaf0008))
 (.leaf (leaf0009))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (leaf0010))
 (.leaf (leaf0011)))
 (.branch 13
 (.leaf (leaf0012))
 (.branch 14
 (.leaf (leaf0013))
 (.leaf (leaf0014)))))
 (.branch 17
 (.branch 16
 (.leaf (leaf0015))
 (.leaf (leaf0016)))
 (.branch 18
 (.leaf (leaf0017))
 (.branch 19
 (.leaf (leaf0018))
 (.leaf (leaf0019)))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record011" 99

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record011" "{\"ridges\":[[0,7],[0,11],[1,21],[2,67],[2,69],[3,515],[4,11],[4,35],[5,67],[5,73],[7,515],[7,530],[8,35],[8,67],[8,97],[8,98],[9,67],[9,515],[9,577],[13,529],[14,517],[14,577],[15,73],[15,97],[21,530],[22,518],[22,578],[23,98],[30,11],[30,21],[31,7],[32,7],[32,11],[33,7],[34,517],[34,518],[38,7],[40,19],[41,11],[41,35],[42,11],[42,35],[44,67],[45,50],[47,35],[47,515],[48,67],[48,529],[48,577],[48,578],[49,515],[49,577],[51,69],[51,76],[51,97],[53,69],[53,73],[53,133],[54,13],[54,517],[54,577],[54,580],[55,388],[56,21],[56,161],[57,21],[57,69],[57,577],[59,517],[59,529],[60,41],[60,168],[61,73],[61,97],[61,104],[61,137],[61,161],[62,41],[63,49],[64,14],[65,98],[68,14],[68,578],[68,580],[69,388],[70,290],[71,22],[71,578],[73,262],[73,518],[73,530],[74,42],[74,50],[74,296],[75,74],[75,98],[75,104],[75,266],[75,290],[75,296],[76,42],[77,50],[79,140]],\"owners\":[[0,7,[1,2,3,35,37,38,39],[31,32,33]],[31,7,[1,2,3,37,38],[0,32,33,35,39]],[32,7,[1,2,3,35,38,39],[0,31,33,37]],[33,7,[1,2,3,35,37,39],[0,31,32,38]],[38,7,[0,2,3,31,32,39],[1,33,35,37]],[0,11,[4,5,40,41,42,43],[30,32,33,34]],[4,11,[0,5,30,32,33,34,43],[40,41,42]],[30,11,[4,5,41,42,43],[0,32,33,34,40]],[32,11,[4,5,40,42,43],[0,30,33,34,41]],[41,11,[0,5,30,33,34,43],[4,32,40,42]],[42,11,[0,5,30,32,34,43],[4,33,40,41]],[54,13,[0,11,30,31,33,50,52,55],[10,34,51]],[64,14,[0,18,31,32,34,65,68],[19,30,66,69]],[68,14,[0,19,30,31,32,64,66,69],[18,34,65]],[40,19,[1,7,36,37,38,48],[6,30,44,45,46]],[71,22,[1,20,30,35,37,64,70,72],[21,36]],[9,67,[2,5,8,36,44],[48]],[51,69,[2,14,36,57],[10,39,53]],[53,69,[2,14,36,39,57],[10,51]],[9,515,[3,7,34,47],[43,49]],[47,515,[3,9,34,43],[7,49]],[49,515,[3,7,34],[9,43,47]],[14,517,[3,13,34,59],[54]],[54,517,[3,13,59],[14,34]],[60,41,[4,15,31,42,51],[16,40,52,62]],[62,41,[4,15,31,40,51],[16,42,52,60]],[74,42,[4,23,31,41,65],[24,40,66,76]],[76,42,[4,23,31,40,65],[24,41,66,74]],[61,73,[5,10,43,54],[15,53]],[75,74,[5,18,43,68],[23,67]],[63,49,[6,35,40,44,47],[17,46,56,60]],[45,50,[25,70,74],[6,35,40,44,47,77]],[74,50,[6,35,44,45,47],[25,40,70,77]],[77,50,[6,35,40,44,47],[25,45,70,74]],[13,529,[7,47,48],[57,59]],[48,529,[13,59],[7,47,57]],[59,529,[7,47,48],[13,57]],[7,530,[21,71,73],[47,48]],[21,530,[7,47,48],[71,73]],[73,530,[7,47,48],[21,71]],[8,97,[15,51,61],[39,44,49]],[15,97,[8,39,44,49],[51,61]],[51,97,[8,44,49],[15,39,61]],[61,97,[8,39,44,49],[15,51]],[8,98,[23,65,75],[39,44,49]],[23,98,[8,39,44,49],[65,75]],[65,98,[8,44,49],[23,39,75]],[75,98,[8,39,44,49],[23,65]],[9,577,[14,54,57],[43,48,49]],[14,577,[9,43,48,49],[54,57]],[48,577,[14,54],[9,43,49,57]],[49,577,[14,54,57],[9,43,48]],[54,577,[9,48,49],[14,43,57]],[57,577,[9,43,49],[14,48,54]],[22,578,[9,43,48,49],[68,71]],[48,578,[22,68],[9,43,49,71]],[68,578,[9,48,49],[22,43,71]],[71,578,[9,43,49],[22,48,68]],[51,76,[18,67,68],[10,53,54,65]],[53,133,[12,37,56,58,59],[11,32,52,55]],[61,137,[11,32,50,55],[16,41,53,60,62]],[79,140,[11,32,50,53],[26,52,69,78]],[54,580,[22,71],[14,57,68]],[68,580,[14,57],[22,54,71]],[61,104,[23,65,75],[15,51]],[75,104,[15,51,61],[23,65]],[56,161,[16,41,61,62],[17,45,52,63]],[61,161,[17,45,56,63],[16,41,52,62]],[60,168,[28,76,79],[16,41,52,61,81]],[73,262,[19,33,66,67,69],[20,38,70,72]],[75,266,[19,33,64,69],[24,42,67,74,76]],[70,290,[24,42,75,76],[25,46,66,77]],[75,290,[25,46,70,77],[24,42,66,76]],[74,296,[28,62,79],[24,42,66,75,81]],[75,296,[28,62,79,81],[24,42,66,74]],[55,388,[27,72,80],[26,58,69,79]],[69,388,[27,58,80],[26,55,72,79]]],\"edges\":[[8,[3,7,9,13,14,34,43,47,48,49,54,57,59]],[34,[7,13,21,47,48,57,59,71,73]],[35,[8,15,23,39,44,49,51,61,65,75]],[41,[9,14,22,43,48,49,54,57,68,71]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-32,-19],[-32,-30],[-34,-8],[-36,-14],[-36,-33],[-37,-22],[-37,-33],[-38,-10],[-39,-9],[-42,-9],[-42,-33],[-42,-38],[-43,-30],[-43,-39],[-43,-40],[-43,-41],[-43,-42],[-44,-43],[-45,-43],[-45,-44],[-46,-2],[-46,-8],[-46,-29],[-46,-34],[-46,-36],[-46,-37],[-46,-39],[-46,-43],[-46,-44],[-46,-45],[-47,-4],[-47,-8],[-47,-10],[-47,-33],[-47,-34],[-47,-38],[-47,-43],[-48,-3],[-48,-6],[-48,-35],[-48,-38],[-48,-39],[-48,-42],[-48,-43],[-48,-46],[-50,-42],[-52,-1],[-52,-32],[-52,-49],[-53,-3],[-53,-15],[-53,-31],[-53,-33],[-53,-50],[-53,-52],[-54,-37],[-54,-49],[-54,-52],[-55,-30],[-55,-44],[-55,-49],[-55,-50],[-55,-51],[-56,-4],[-56,-33],[-56,-35],[-56,-36],[-56,-43],[-56,-53],[-57,-37],[-57,-49],[-57,-55],[-58,-2],[-58,-29],[-58,-36],[-58,-37],[-58,-49],[-58,-55],[-58,-56],[-58,-57],[-59,-29],[-59,-39],[-59,-40],[-59,-44],[-59,-49],[-59,-51],[-59,-55],[-60,-16],[-60,-59],[-61,-51],[-61,-59],[-61,-60],[-62,-44],[-62,-55],[-62,-59],[-63,-59],[-64,-55],[-65,-55],[-65,-63],[-66,-30],[-66,-31],[-66,-32],[-66,-63],[-67,-3],[-67,-32],[-67,-33],[-67,-64],[-67,-66],[-68,-54],[-68,-63],[-68,-66],[-69,-30],[-69,-45],[-69,-50],[-69,-51],[-69,-63],[-69,-64],[-69,-65],[-70,-4],[-70,-33],[-70,-35],[-70,-43],[-70,-56],[-70,-67],[-71,-63],[-71,-69],[-72,-2],[-72,-29],[-72,-35],[-72,-36],[-72,-37],[-72,-63],[-72,-69],[-72,-70],[-72,-71],[-73,-26],[-73,-41],[-73,-45],[-73,-63],[-73,-65],[-73,-69],[-74,-5],[-74,-30],[-74,-39],[-74,-40],[-74,-41],[-74,-73],[-75,-61],[-75,-73],[-75,-74],[-76,-31],[-76,-36],[-76,-45],[-76,-62],[-76,-68],[-76,-69],[-76,-73],[-77,-54],[-77,-57],[-77,-68],[-77,-71],[-78,-30],[-78,-50],[-78,-51],[-78,-54],[-78,-61],[-78,-64],[-78,-65],[-78,-68],[-78,-75],[-78,-77],[-79,-50],[-79,-51],[-79,-55],[-79,-57],[-79,-62],[-79,-64],[-79,-65],[-79,-69],[-79,-71],[-79,-76],[-79,-77],[-79,-78],[-80,-61],[-80,-62],[-80,-75],[-80,-76],[-80,-78],[-80,-79],[-1,2,3,4,34,36,37,38],[-30,2,3,4,36,37],[-31,2,3,4,34,37,38],[-32,2,3,4,34,36,38],[-37,1,3,4,30,31,38],[-1,5,6,39,40,41,42],[-5,1,6,29,31,32,33,42],[-29,5,6,40,41,42],[-31,5,6,39,41,42],[-40,1,6,29,32,33,42],[-41,1,6,29,31,33,42],[-53,1,12,29,30,32,49,51,54],[-63,1,19,30,31,33,64,67],[-67,1,20,29,30,31,63,65,68],[-39,2,8,35,36,37,47],[-2,-55,-56],[-29,-55,-56],[-70,2,21,29,34,36,63,69,71],[-10,3,6,9,35,43],[-3,-9,-10],[-3,-10,-43],[-6,-9,-47],[-50,3,15,35,56],[-52,3,15,35,38,56],[-3,-52,-56],[-10,4,8,33,46],[-46,4,10,33,42],[-48,4,8,33],[-4,-8,-10],[-4,-8,-48],[-4,-10,-46],[-15,4,14,33,58],[-53,4,14,58],[-15,-33,-58],[-23,-33,-72],[-5,-9,-46],[-9,-40,-46],[-9,-41,-46],[-59,5,16,30,41,50],[-61,5,16,30,39,50],[-73,5,24,30,40,64],[-75,5,24,30,39,64],[-60,6,11,42,53],[-6,-16,-52],[-74,6,19,42,67],[-62,7,34,39,43,46],[-44,26,69,73],[-73,7,34,43,44,46],[-76,7,34,39,43,46],[-14,8,46,47],[-47,14,58],[-58,8,46,47],[-8,22,70,72],[-22,8,46,47],[-72,8,46,47],[-9,16,50,60],[-16,9,38,43,48],[-50,9,43,48],[-60,9,38,43,48],[-9,24,64,74],[-24,9,38,43,48],[-64,9,43,48],[-74,9,38,43,48],[-10,15,53,56],[-15,10,42,47,48],[-47,15,53],[-48,15,53,56],[-53,10,47,48],[-56,10,42,48],[-23,10,42,47,48],[-47,23,67],[-67,10,47,48],[-70,10,42,48],[-50,19,66,67],[-52,13,36,55,57,58],[-60,12,31,49,54],[-78,12,31,49,52],[-53,23,70],[-67,15,56],[-60,24,64,74],[-74,16,50,60],[-55,17,40,60,61],[-60,18,44,55,62],[-59,28,75,78],[-72,20,32,65,66,68],[-74,20,32,63,68],[-69,25,41,74,75],[-74,26,45,69,76],[-73,28,61,78],[-74,28,61,78,80],[-54,27,71,79],[-68,27,57,79],[-81,35,43,46,47,48],[-82,36,56,58],[-83,30,50,51,52,60],[-84,33,38,42,53,67],[-85,37,70,72],[-86,64,65,66,74],[-87,32,41,45,54,57,61,62],[-88,29,39,49,59,63,73,77,80],[-89,31,40,44,68,71,75,76],[-90,34,55,69,78,79],[-91,81],[-91,82],[-92,84],[-92,85],[-93,83],[-93,92],[-94,91],[-94,93],[-95,86],[-95,87],[-96,89],[-96,90],[-97,88],[-97,96],[-98,95],[-98,97],[-99,94],[-99,98],[99],[-7,-8,-12,-24,-48,-53,-58,-60,-62,-66,-70,-71,-73,-78],[-7,-8,-12,-24,-48,-53,-58,-60,-62,-66,-69,-70,-75,-77],[-8,-16,-17,-27,-45,-48,-52,-55,-56,-67,-68,-72,-74,-80],[-8,-13,-16,-28,-45,-48,-52,-56,-59,-67,-68,-72,-74,-79],[-8,-11,-12,-27,-45,-48,-55,-56,-60,-67,-68,-72,-74,-80],[-8,-11,-18,-28,-45,-48,-49,-56,-60,-67,-68,-72,-74,-79],[-8,-15,-16,-28,-45,-48,-52,-58,-59,-67,-68,-72,-74,-79],[-9,-10,-12,-24,-46,-53,-58,-60,-62,-66,-70,-71,-73,-78],[-9,-10,-12,-24,-46,-53,-58,-60,-62,-66,-69,-70,-75,-77],[-9,-15,-16,-28,-45,-47,-52,-58,-59,-67,-68,-72,-74,-79],[-7,-8,-16,-20,-48,-52,-56,-57,-59,-67,-72,-74,-76,-78],[-7,-8,-16,-20,-48,-52,-55,-56,-61,-67,-72,-74,-76,-77],[-8,-24,-25,-27,-44,-48,-53,-54,-58,-60,-66,-69,-70,-80],[-8,-21,-24,-28,-44,-48,-53,-54,-58,-60,-66,-70,-73,-79],[-8,-19,-20,-27,-44,-48,-53,-54,-58,-60,-69,-70,-74,-80],[-8,-19,-26,-28,-44,-48,-53,-54,-58,-60,-63,-70,-74,-79],[-8,-23,-24,-28,-44,-48,-53,-54,-58,-60,-66,-72,-73,-79],[-9,-10,-16,-20,-46,-52,-56,-57,-59,-67,-72,-74,-76,-78],[-9,-10,-16,-20,-46,-52,-55,-56,-61,-67,-72,-74,-76,-77],[-9,-23,-24,-28,-44,-47,-53,-54,-58,-60,-66,-72,-73,-79],[4,8,10,14,15,33,42,46,47,48,53,56,58],[8,14,22,46,47,56,58,70,72],[9,16,24,38,43,48,50,60,64,74],[10,15,23,42,47,48,53,56,67,70]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":18},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":7},{\"tag\":\"incompatible\",\"a\":37,\"b\":13},{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":21},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":9},{\"tag\":\"incompatible\",\"a\":40,\"b\":8},{\"tag\":\"incompatible\",\"a\":43,\"b\":8},{\"tag\":\"incompatible\",\"a\":43,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":31},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":1},{\"tag\":\"incompatible\",\"a\":47,\"b\":7},{\"tag\":\"incompatible\",\"a\":47,\"b\":30},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":47,\"b\":37},{\"tag\":\"incompatible\",\"a\":47,\"b\":38},{\"tag\":\"incompatible\",\"a\":47,\"b\":40},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":3},{\"tag\":\"incompatible\",\"a\":48,\"b\":7},{\"tag\":\"incompatible\",\"a\":48,\"b\":9},{\"tag\":\"incompatible\",\"a\":48,\"b\":34},{\"tag\":\"incompatible\",\"a\":48,\"b\":35},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":2},{\"tag\":\"incompatible\",\"a\":49,\"b\":5},{\"tag\":\"incompatible\",\"a\":49,\"b\":36},{\"tag\":\"incompatible\",\"a\":49,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":40},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":43},{\"tag\":\"incompatible\",\"a\":53,\"b\":0},{\"tag\":\"incompatible\",\"a\":53,\"b\":33},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":54,\"b\":2},{\"tag\":\"incompatible\",\"a\":54,\"b\":14},{\"tag\":\"incompatible\",\"a\":54,\"b\":32},{\"tag\":\"incompatible\",\"a\":54,\"b\":34},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":38},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":31},{\"tag\":\"incompatible\",\"a\":56,\"b\":45},{\"tag\":\"incompatible\",\"a\":56,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":3},{\"tag\":\"incompatible\",\"a\":57,\"b\":34},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":38},{\"tag\":\"incompatible\",\"a\":58,\"b\":50},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":1},{\"tag\":\"incompatible\",\"a\":59,\"b\":30},{\"tag\":\"incompatible\",\"a\":59,\"b\":37},{\"tag\":\"incompatible\",\"a\":59,\"b\":38},{\"tag\":\"incompatible\",\"a\":59,\"b\":50},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":30},{\"tag\":\"incompatible\",\"a\":60,\"b\":40},{\"tag\":\"incompatible\",\"a\":60,\"b\":41},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":50},{\"tag\":\"incompatible\",\"a\":60,\"b\":52},{\"tag\":\"incompatible\",\"a\":60,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":15},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":52},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":45},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":31},{\"tag\":\"incompatible\",\"a\":67,\"b\":32},{\"tag\":\"incompatible\",\"a\":67,\"b\":33},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":2},{\"tag\":\"incompatible\",\"a\":68,\"b\":33},{\"tag\":\"incompatible\",\"a\":68,\"b\":34},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":55},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":31},{\"tag\":\"incompatible\",\"a\":70,\"b\":46},{\"tag\":\"incompatible\",\"a\":70,\"b\":51},{\"tag\":\"incompatible\",\"a\":70,\"b\":52},{\"tag\":\"incompatible\",\"a\":70,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":3},{\"tag\":\"incompatible\",\"a\":71,\"b\":34},{\"tag\":\"incompatible\",\"a\":71,\"b\":36},{\"tag\":\"incompatible\",\"a\":71,\"b\":44},{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":72,\"b\":64},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":1},{\"tag\":\"incompatible\",\"a\":73,\"b\":30},{\"tag\":\"incompatible\",\"a\":73,\"b\":36},{\"tag\":\"incompatible\",\"a\":73,\"b\":37},{\"tag\":\"incompatible\",\"a\":73,\"b\":38},{\"tag\":\"incompatible\",\"a\":73,\"b\":64},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":25},{\"tag\":\"incompatible\",\"a\":74,\"b\":42},{\"tag\":\"incompatible\",\"a\":74,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":64},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":4},{\"tag\":\"incompatible\",\"a\":75,\"b\":31},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":41},{\"tag\":\"incompatible\",\"a\":75,\"b\":42},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":62},{\"tag\":\"incompatible\",\"a\":76,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":32},{\"tag\":\"incompatible\",\"a\":77,\"b\":37},{\"tag\":\"incompatible\",\"a\":77,\"b\":46},{\"tag\":\"incompatible\",\"a\":77,\"b\":63},{\"tag\":\"incompatible\",\"a\":77,\"b\":69},{\"tag\":\"incompatible\",\"a\":77,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":78,\"b\":55},{\"tag\":\"incompatible\",\"a\":78,\"b\":58},{\"tag\":\"incompatible\",\"a\":78,\"b\":69},{\"tag\":\"incompatible\",\"a\":78,\"b\":72},{\"tag\":\"incompatible\",\"a\":79,\"b\":31},{\"tag\":\"incompatible\",\"a\":79,\"b\":51},{\"tag\":\"incompatible\",\"a\":79,\"b\":52},{\"tag\":\"incompatible\",\"a\":79,\"b\":55},{\"tag\":\"incompatible\",\"a\":79,\"b\":62},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"incompatible\",\"a\":79,\"b\":66},{\"tag\":\"incompatible\",\"a\":79,\"b\":69},{\"tag\":\"incompatible\",\"a\":79,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":51},{\"tag\":\"incompatible\",\"a\":80,\"b\":52},{\"tag\":\"incompatible\",\"a\":80,\"b\":56},{\"tag\":\"incompatible\",\"a\":80,\"b\":58},{\"tag\":\"incompatible\",\"a\":80,\"b\":63},{\"tag\":\"incompatible\",\"a\":80,\"b\":65},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"incompatible\",\"a\":80,\"b\":72},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":62},{\"tag\":\"incompatible\",\"a\":81,\"b\":63},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"mate\",\"ridge\":7,\"a\":0,\"owners\":[1,2,3,35,37,38,39]},{\"tag\":\"mate\",\"ridge\":7,\"a\":31,\"owners\":[1,2,3,37,38]},{\"tag\":\"mate\",\"ridge\":7,\"a\":32,\"owners\":[1,2,3,35,38,39]},{\"tag\":\"mate\",\"ridge\":7,\"a\":33,\"owners\":[1,2,3,35,37,39]},{\"tag\":\"mate\",\"ridge\":7,\"a\":38,\"owners\":[0,2,3,31,32,39]},{\"tag\":\"mate\",\"ridge\":11,\"a\":0,\"owners\":[4,5,40,41,42,43]},{\"tag\":\"mate\",\"ridge\":11,\"a\":4,\"owners\":[0,5,30,32,33,34,43]},{\"tag\":\"mate\",\"ridge\":11,\"a\":30,\"owners\":[4,5,41,42,43]},{\"tag\":\"mate\",\"ridge\":11,\"a\":32,\"owners\":[4,5,40,42,43]},{\"tag\":\"mate\",\"ridge\":11,\"a\":41,\"owners\":[0,5,30,33,34,43]},{\"tag\":\"mate\",\"ridge\":11,\"a\":42,\"owners\":[0,5,30,32,34,43]},{\"tag\":\"mate\",\"ridge\":13,\"a\":54,\"owners\":[0,11,30,31,33,50,52,55]},{\"tag\":\"mate\",\"ridge\":14,\"a\":64,\"owners\":[0,18,31,32,34,65,68]},{\"tag\":\"mate\",\"ridge\":14,\"a\":68,\"owners\":[0,19,30,31,32,64,66,69]},{\"tag\":\"mate\",\"ridge\":19,\"a\":40,\"owners\":[1,7,36,37,38,48]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[1,56,57]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[30,56,57]},{\"tag\":\"mate\",\"ridge\":22,\"a\":71,\"owners\":[1,20,30,35,37,64,70,72]},{\"tag\":\"mate\",\"ridge\":67,\"a\":9,\"owners\":[2,5,8,36,44]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[2,8,9]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[2,9,44]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[5,8,48]},{\"tag\":\"mate\",\"ridge\":69,\"a\":51,\"owners\":[2,14,36,57]},{\"tag\":\"mate\",\"ridge\":69,\"a\":53,\"owners\":[2,14,36,39,57]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[2,53,57]},{\"tag\":\"mate\",\"ridge\":515,\"a\":9,\"owners\":[3,7,34,47]},{\"tag\":\"mate\",\"ridge\":515,\"a\":47,\"owners\":[3,9,34,43]},{\"tag\":\"mate\",\"ridge\":515,\"a\":49,\"owners\":[3,7,34]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[3,7,9]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[3,7,49]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[3,9,47]},{\"tag\":\"mate\",\"ridge\":517,\"a\":14,\"owners\":[3,13,34,59]},{\"tag\":\"mate\",\"ridge\":517,\"a\":54,\"owners\":[3,13,59]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[14,34,59]},{\"tag\":\"three\",\"ridge\":518,\"vertices\":[22,34,73]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[4,8,47]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[8,41,47]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[8,42,47]},{\"tag\":\"mate\",\"ridge\":41,\"a\":60,\"owners\":[4,15,31,42,51]},{\"tag\":\"mate\",\"ridge\":41,\"a\":62,\"owners\":[4,15,31,40,51]},{\"tag\":\"mate\",\"ridge\":42,\"a\":74,\"owners\":[4,23,31,41,65]},{\"tag\":\"mate\",\"ridge\":42,\"a\":76,\"owners\":[4,23,31,40,65]},{\"tag\":\"mate\",\"ridge\":73,\"a\":61,\"owners\":[5,10,43,54]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[5,15,53]},{\"tag\":\"mate\",\"ridge\":74,\"a\":75,\"owners\":[5,18,43,68]},{\"tag\":\"mate\",\"ridge\":49,\"a\":63,\"owners\":[6,35,40,44,47]},{\"tag\":\"mate\",\"ridge\":50,\"a\":45,\"owners\":[25,70,74]},{\"tag\":\"mate\",\"ridge\":50,\"a\":74,\"owners\":[6,35,44,45,47]},{\"tag\":\"mate\",\"ridge\":50,\"a\":77,\"owners\":[6,35,40,44,47]},{\"tag\":\"mate\",\"ridge\":529,\"a\":13,\"owners\":[7,47,48]},{\"tag\":\"mate\",\"ridge\":529,\"a\":48,\"owners\":[13,59]},{\"tag\":\"mate\",\"ridge\":529,\"a\":59,\"owners\":[7,47,48]},{\"tag\":\"mate\",\"ridge\":530,\"a\":7,\"owners\":[21,71,73]},{\"tag\":\"mate\",\"ridge\":530,\"a\":21,\"owners\":[7,47,48]},{\"tag\":\"mate\",\"ridge\":530,\"a\":73,\"owners\":[7,47,48]},{\"tag\":\"mate\",\"ridge\":97,\"a\":8,\"owners\":[15,51,61]},{\"tag\":\"mate\",\"ridge\":97,\"a\":15,\"owners\":[8,39,44,49]},{\"tag\":\"mate\",\"ridge\":97,\"a\":51,\"owners\":[8,44,49]},{\"tag\":\"mate\",\"ridge\":97,\"a\":61,\"owners\":[8,39,44,49]},{\"tag\":\"mate\",\"ridge\":98,\"a\":8,\"owners\":[23,65,75]},{\"tag\":\"mate\",\"ridge\":98,\"a\":23,\"owners\":[8,39,44,49]},{\"tag\":\"mate\",\"ridge\":98,\"a\":65,\"owners\":[8,44,49]},{\"tag\":\"mate\",\"ridge\":98,\"a\":75,\"owners\":[8,39,44,49]},{\"tag\":\"mate\",\"ridge\":577,\"a\":9,\"owners\":[14,54,57]},{\"tag\":\"mate\",\"ridge\":577,\"a\":14,\"owners\":[9,43,48,49]},{\"tag\":\"mate\",\"ridge\":577,\"a\":48,\"owners\":[14,54]},{\"tag\":\"mate\",\"ridge\":577,\"a\":49,\"owners\":[14,54,57]},{\"tag\":\"mate\",\"ridge\":577,\"a\":54,\"owners\":[9,48,49]},{\"tag\":\"mate\",\"ridge\":577,\"a\":57,\"owners\":[9,43,49]},{\"tag\":\"mate\",\"ridge\":578,\"a\":22,\"owners\":[9,43,48,49]},{\"tag\":\"mate\",\"ridge\":578,\"a\":48,\"owners\":[22,68]},{\"tag\":\"mate\",\"ridge\":578,\"a\":68,\"owners\":[9,48,49]},{\"tag\":\"mate\",\"ridge\":578,\"a\":71,\"owners\":[9,43,49]},{\"tag\":\"mate\",\"ridge\":76,\"a\":51,\"owners\":[18,67,68]},{\"tag\":\"mate\",\"ridge\":133,\"a\":53,\"owners\":[12,37,56,58,59]},{\"tag\":\"mate\",\"ridge\":137,\"a\":61,\"owners\":[11,32,50,55]},{\"tag\":\"mate\",\"ridge\":140,\"a\":79,\"owners\":[11,32,50,53]},{\"tag\":\"mate\",\"ridge\":580,\"a\":54,\"owners\":[22,71]},{\"tag\":\"mate\",\"ridge\":580,\"a\":68,\"owners\":[14,57]},{\"tag\":\"mate\",\"ridge\":104,\"a\":61,\"owners\":[23,65,75]},{\"tag\":\"mate\",\"ridge\":104,\"a\":75,\"owners\":[15,51,61]},{\"tag\":\"mate\",\"ridge\":161,\"a\":56,\"owners\":[16,41,61,62]},{\"tag\":\"mate\",\"ridge\":161,\"a\":61,\"owners\":[17,45,56,63]},{\"tag\":\"mate\",\"ridge\":168,\"a\":60,\"owners\":[28,76,79]},{\"tag\":\"mate\",\"ridge\":262,\"a\":73,\"owners\":[19,33,66,67,69]},{\"tag\":\"mate\",\"ridge\":266,\"a\":75,\"owners\":[19,33,64,69]},{\"tag\":\"mate\",\"ridge\":290,\"a\":70,\"owners\":[24,42,75,76]},{\"tag\":\"mate\",\"ridge\":290,\"a\":75,\"owners\":[25,46,70,77]},{\"tag\":\"mate\",\"ridge\":296,\"a\":74,\"owners\":[28,62,79]},{\"tag\":\"mate\",\"ridge\":296,\"a\":75,\"owners\":[28,62,79,81]},{\"tag\":\"mate\",\"ridge\":388,\"a\":55,\"owners\":[27,72,80]},{\"tag\":\"mate\",\"ridge\":388,\"a\":69,\"owners\":[27,58,80]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[36,44,47,48,49],\"full_literals\":[-81,35,43,46,47,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[37,57,59],\"full_literals\":[-82,36,56,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[31,51,52,53,61],\"full_literals\":[-83,30,50,51,52,60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[34,39,43,54,68],\"full_literals\":[-84,33,38,42,53,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[38,71,73],\"full_literals\":[-85,37,70,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[65,66,67,75],\"full_literals\":[-86,64,65,66,74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[33,42,46,55,58,62,63],\"full_literals\":[-87,32,41,45,54,57,61,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[30,40,50,60,64,74,78,81],\"full_literals\":[-88,29,39,49,59,63,73,77,80]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[32,41,45,69,72,76,77],\"full_literals\":[-89,31,40,44,68,71,75,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[35,56,70,79,80],\"full_literals\":[-90,34,55,69,78,79]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-91,81,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-91,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-92,84,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-93,83,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-93,false,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-94,91,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-94,false,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-95,86,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-95,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-96,89,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-96,false,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-97,88,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-97,false,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-98,95,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-98,false,97],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-99,94,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-99,false,98],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[6,7,11,23,49,54,59,61,63,67,71,72,74,79]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[6,7,11,23,49,54,59,61,63,67,70,71,76,78]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[7,15,16,27,46,49,53,56,57,68,69,73,75,81]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[7,12,15,28,46,49,53,57,60,68,69,73,75,80]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[7,10,11,27,46,49,56,57,61,68,69,73,75,81]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[7,10,17,28,46,49,50,57,61,68,69,73,75,80]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[7,14,15,28,46,49,53,59,60,68,69,73,75,80]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[8,9,11,23,47,54,59,61,63,67,71,72,74,79]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[8,9,11,23,47,54,59,61,63,67,70,71,76,78]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[8,14,15,28,46,48,53,59,60,68,69,73,75,80]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[6,7,15,19,49,53,57,58,60,68,73,75,77,79]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[6,7,15,19,49,53,56,57,62,68,73,75,77,78]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[7,23,24,27,45,49,54,55,59,61,67,70,71,81]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[7,20,23,28,45,49,54,55,59,61,67,71,74,80]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[7,18,19,27,45,49,54,55,59,61,70,71,75,81]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[7,18,25,28,45,49,54,55,59,61,64,71,75,80]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[7,22,23,28,45,49,54,55,59,61,67,73,74,80]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[8,9,15,19,47,53,57,58,60,68,73,75,77,79]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[8,9,15,19,47,53,56,57,62,68,73,75,77,78]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[8,22,23,28,45,48,54,55,59,61,67,73,74,80]},{\"tag\":\"edge\",\"edge\":8,\"owners\":[3,7,9,13,14,34,43,47,48,49,54,57,59]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[7,13,21,47,48,57,59,71,73]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[8,15,23,39,44,49,51,61,65,75]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[9,14,22,43,48,49,54,57,68,71]}]}"
  "p cnf 99 334\n-32 -19 0\n-32 -30 0\n-34 -8 0\n-36 -14 0\n-36 -33 0\n-37 -22 0\n-37 -33 0\n-38 -10 0\n-39 -9 0\n-42 -9 0\n-42 -33 0\n-42 -38 0\n-43 -30 0\n-43 -39 0\n-43 -40 0\n-43 -41 0\n-43 -42 0\n-44 -43 0\n-45 -43 0\n-45 -44 0\n-46 -2 0\n-46 -8 0\n-46 -29 0\n-46 -34 0\n-46 -36 0\n-46 -37 0\n-46 -39 0\n-46 -43 0\n-46 -44 0\n-46 -45 0\n-47 -4 0\n-47 -8 0\n-47 -10 0\n-47 -33 0\n-47 -34 0\n-47 -38 0\n-47 -43 0\n-48 -3 0\n-48 -6 0\n-48 -35 0\n-48 -38 0\n-48 -39 0\n-48 -42 0\n-48 -43 0\n-48 -46 0\n-50 -42 0\n-52 -1 0\n-52 -32 0\n-52 -49 0\n-53 -3 0\n-53 -15 0\n-53 -31 0\n-53 -33 0\n-53 -50 0\n-53 -52 0\n-54 -37 0\n-54 -49 0\n-54 -52 0\n-55 -30 0\n-55 -44 0\n-55 -49 0\n-55 -50 0\n-55 -51 0\n-56 -4 0\n-56 -33 0\n-56 -35 0\n-56 -36 0\n-56 -43 0\n-56 -53 0\n-57 -37 0\n-57 -49 0\n-57 -55 0\n-58 -2 0\n-58 -29 0\n-58 -36 0\n-58 -37 0\n-58 -49 0\n-58 -55 0\n-58 -56 0\n-58 -57 0\n-59 -29 0\n-59 -39 0\n-59 -40 0\n-59 -44 0\n-59 -49 0\n-59 -51 0\n-59 -55 0\n-60 -16 0\n-60 -59 0\n-61 -51 0\n-61 -59 0\n-61 -60 0\n-62 -44 0\n-62 -55 0\n-62 -59 0\n-63 -59 0\n-64 -55 0\n-65 -55 0\n-65 -63 0\n-66 -30 0\n-66 -31 0\n-66 -32 0\n-66 -63 0\n-67 -3 0\n-67 -32 0\n-67 -33 0\n-67 -64 0\n-67 -66 0\n-68 -54 0\n-68 -63 0\n-68 -66 0\n-69 -30 0\n-69 -45 0\n-69 -50 0\n-69 -51 0\n-69 -63 0\n-69 -64 0\n-69 -65 0\n-70 -4 0\n-70 -33 0\n-70 -35 0\n-70 -43 0\n-70 -56 0\n-70 -67 0\n-71 -63 0\n-71 -69 0\n-72 -2 0\n-72 -29 0\n-72 -35 0\n-72 -36 0\n-72 -37 0\n-72 -63 0\n-72 -69 0\n-72 -70 0\n-72 -71 0\n-73 -26 0\n-73 -41 0\n-73 -45 0\n-73 -63 0\n-73 -65 0\n-73 -69 0\n-74 -5 0\n-74 -30 0\n-74 -39 0\n-74 -40 0\n-74 -41 0\n-74 -73 0\n-75 -61 0\n-75 -73 0\n-75 -74 0\n-76 -31 0\n-76 -36 0\n-76 -45 0\n-76 -62 0\n-76 -68 0\n-76 -69 0\n-76 -73 0\n-77 -54 0\n-77 -57 0\n-77 -68 0\n-77 -71 0\n-78 -30 0\n-78 -50 0\n-78 -51 0\n-78 -54 0\n-78 -61 0\n-78 -64 0\n-78 -65 0\n-78 -68 0\n-78 -75 0\n-78 -77 0\n-79 -50 0\n-79 -51 0\n-79 -55 0\n-79 -57 0\n-79 -62 0\n-79 -64 0\n-79 -65 0\n-79 -69 0\n-79 -71 0\n-79 -76 0\n-79 -77 0\n-79 -78 0\n-80 -61 0\n-80 -62 0\n-80 -75 0\n-80 -76 0\n-80 -78 0\n-80 -79 0\n-1 2 3 4 34 36 37 38 0\n-30 2 3 4 36 37 0\n-31 2 3 4 34 37 38 0\n-32 2 3 4 34 36 38 0\n-37 1 3 4 30 31 38 0\n-1 5 6 39 40 41 42 0\n-5 1 6 29 31 32 33 42 0\n-29 5 6 40 41 42 0\n-31 5 6 39 41 42 0\n-40 1 6 29 32 33 42 0\n-41 1 6 29 31 33 42 0\n-53 1 12 29 30 32 49 51 54 0\n-63 1 19 30 31 33 64 67 0\n-67 1 20 29 30 31 63 65 68 0\n-39 2 8 35 36 37 47 0\n-2 -55 -56 0\n-29 -55 -56 0\n-70 2 21 29 34 36 63 69 71 0\n-10 3 6 9 35 43 0\n-3 -9 -10 0\n-3 -10 -43 0\n-6 -9 -47 0\n-50 3 15 35 56 0\n-52 3 15 35 38 56 0\n-3 -52 -56 0\n-10 4 8 33 46 0\n-46 4 10 33 42 0\n-48 4 8 33 0\n-4 -8 -10 0\n-4 -8 -48 0\n-4 -10 -46 0\n-15 4 14 33 58 0\n-53 4 14 58 0\n-15 -33 -58 0\n-23 -33 -72 0\n-5 -9 -46 0\n-9 -40 -46 0\n-9 -41 -46 0\n-59 5 16 30 41 50 0\n-61 5 16 30 39 50 0\n-73 5 24 30 40 64 0\n-75 5 24 30 39 64 0\n-60 6 11 42 53 0\n-6 -16 -52 0\n-74 6 19 42 67 0\n-62 7 34 39 43 46 0\n-44 26 69 73 0\n-73 7 34 43 44 46 0\n-76 7 34 39 43 46 0\n-14 8 46 47 0\n-47 14 58 0\n-58 8 46 47 0\n-8 22 70 72 0\n-22 8 46 47 0\n-72 8 46 47 0\n-9 16 50 60 0\n-16 9 38 43 48 0\n-50 9 43 48 0\n-60 9 38 43 48 0\n-9 24 64 74 0\n-24 9 38 43 48 0\n-64 9 43 48 0\n-74 9 38 43 48 0\n-10 15 53 56 0\n-15 10 42 47 48 0\n-47 15 53 0\n-48 15 53 56 0\n-53 10 47 48 0\n-56 10 42 48 0\n-23 10 42 47 48 0\n-47 23 67 0\n-67 10 47 48 0\n-70 10 42 48 0\n-50 19 66 67 0\n-52 13 36 55 57 58 0\n-60 12 31 49 54 0\n-78 12 31 49 52 0\n-53 23 70 0\n-67 15 56 0\n-60 24 64 74 0\n-74 16 50 60 0\n-55 17 40 60 61 0\n-60 18 44 55 62 0\n-59 28 75 78 0\n-72 20 32 65 66 68 0\n-74 20 32 63 68 0\n-69 25 41 74 75 0\n-74 26 45 69 76 0\n-73 28 61 78 0\n-74 28 61 78 80 0\n-54 27 71 79 0\n-68 27 57 79 0\n-81 35 43 46 47 48 0\n-82 36 56 58 0\n-83 30 50 51 52 60 0\n-84 33 38 42 53 67 0\n-85 37 70 72 0\n-86 64 65 66 74 0\n-87 32 41 45 54 57 61 62 0\n-88 29 39 49 59 63 73 77 80 0\n-89 31 40 44 68 71 75 76 0\n-90 34 55 69 78 79 0\n-91 81 0\n-91 82 0\n-92 84 0\n-92 85 0\n-93 83 0\n-93 92 0\n-94 91 0\n-94 93 0\n-95 86 0\n-95 87 0\n-96 89 0\n-96 90 0\n-97 88 0\n-97 96 0\n-98 95 0\n-98 97 0\n-99 94 0\n-99 98 0\n99 0\n-7 -8 -12 -24 -48 -53 -58 -60 -62 -66 -70 -71 -73 -78 0\n-7 -8 -12 -24 -48 -53 -58 -60 -62 -66 -69 -70 -75 -77 0\n-8 -16 -17 -27 -45 -48 -52 -55 -56 -67 -68 -72 -74 -80 0\n-8 -13 -16 -28 -45 -48 -52 -56 -59 -67 -68 -72 -74 -79 0\n-8 -11 -12 -27 -45 -48 -55 -56 -60 -67 -68 -72 -74 -80 0\n-8 -11 -18 -28 -45 -48 -49 -56 -60 -67 -68 -72 -74 -79 0\n-8 -15 -16 -28 -45 -48 -52 -58 -59 -67 -68 -72 -74 -79 0\n-9 -10 -12 -24 -46 -53 -58 -60 -62 -66 -70 -71 -73 -78 0\n-9 -10 -12 -24 -46 -53 -58 -60 -62 -66 -69 -70 -75 -77 0\n-9 -15 -16 -28 -45 -47 -52 -58 -59 -67 -68 -72 -74 -79 0\n-7 -8 -16 -20 -48 -52 -56 -57 -59 -67 -72 -74 -76 -78 0\n-7 -8 -16 -20 -48 -52 -55 -56 -61 -67 -72 -74 -76 -77 0\n-8 -24 -25 -27 -44 -48 -53 -54 -58 -60 -66 -69 -70 -80 0\n-8 -21 -24 -28 -44 -48 -53 -54 -58 -60 -66 -70 -73 -79 0\n-8 -19 -20 -27 -44 -48 -53 -54 -58 -60 -69 -70 -74 -80 0\n-8 -19 -26 -28 -44 -48 -53 -54 -58 -60 -63 -70 -74 -79 0\n-8 -23 -24 -28 -44 -48 -53 -54 -58 -60 -66 -72 -73 -79 0\n-9 -10 -16 -20 -46 -52 -56 -57 -59 -67 -72 -74 -76 -78 0\n-9 -10 -16 -20 -46 -52 -55 -56 -61 -67 -72 -74 -76 -77 0\n-9 -23 -24 -28 -44 -47 -53 -54 -58 -60 -66 -72 -73 -79 0\n4 8 10 14 15 33 42 46 47 48 53 56 58 0\n8 14 22 46 47 56 58 70 72 0\n9 16 24 38 43 48 50 60 64 74 0\n10 15 23 42 47 48 53 56 67 70 0\n"
  "335 94 0 310 308 0\n336 98 0 310 309 0\n337 91 0 335 298 0\n338 93 0 335 299 0\n339 95 0 336 306 0\n340 97 0 336 307 0\n341 81 0 337 292 0\n342 82 0 337 293 0\n343 83 0 338 296 0\n344 92 0 338 297 0\n345 86 0 339 300 0\n346 87 0 339 301 0\n347 88 0 340 304 0\n348 96 0 340 305 0\n349 84 0 344 294 0\n350 85 0 344 295 0\n351 89 0 348 302 0\n352 90 0 348 303 0\n353 -33 0 342 350 5 7 11 34 53 65 106 120 283 286 223 224 253 256 334 0\n354 47 4 8 48 10 42 0 353 216 258 257 254 241 239 331 0\n355 58 -53 4 56 0 342 222 283 4 0\n356 9 50 38 43 48 0 251 246 252 250 248 333 0\n357 -64 69 55 34 0 352 167 177 291 0\n358 -78 59 61 41 40 39 71 63 32 57 49 29 31 0 347 346 351 165 169 170 171 188 289 138 157 288 290 93 0\n359 74 -54 -28 -73 -79 -60 40 -9 -72 -58 -23 -53 -47 0 345 351 149 181 178 35 78 133 357 135 52 249 287 111 290 330 0\n360 16 41 40 5 -9 30 -72 32 -58 -23 -53 -47 0 352 347 346 9 135 133 132 80 78 77 74 54 52 35 245 229 228 358 291 176 181 182 189 289 136 138 278 288 359 277 0\n361 15 -47 4 43 56 70 48 42 0 350 353 343 352 36 35 268 255 260 50 52 54 55 355 73 74 75 76 78 190 193 286 191 133 356 211 196 199 200 360 88 284 164 173 291 0\n362 -78 71 63 41 40 31 57 49 29 39 32 0 351 346 165 166 169 170 358 84 95 290 288 153 0\n363 -58 -9 -15 -47 4 70 42 0 349 350 353 352 345 347 351 343 346 211 9 36 51 285 108 107 105 104 35 73 74 75 76 77 78 80 190 192 199 200 286 191 196 132 133 135 362 291 172 173 176 178 181 182 189 287 147 150 289 84 89 91 228 273 290 284 320 109 288 0\n364 58 -47 56 0 342 240 283 4 0\n365 4 8 43 48 10 42 0 258 262 354 36 361 364 363 247 356 0\n366 47 48 10 42 0 258 262 257 261 259 254 334 0\n367 48 10 42 0 366 31 32 365 37 0\n368 -58 -15 4 -48 42 0 349 350 353 352 345 347 351 343 346 41 51 285 124 108 107 105 217 3 42 39 38 73 74 75 76 77 78 80 190 192 199 200 286 191 196 132 133 135 362 291 172 173 176 178 181 182 189 287 147 150 289 84 89 91 228 273 290 284 317 109 288 0\n369 -15 56 4 -48 42 0 342 353 368 283 221 4 0\n370 70 5 30 41 40 32 -58 50 52 -53 -8 -48 0 350 352 343 347 346 345 351 80 78 77 76 74 52 3 42 267 286 132 133 135 357 362 291 173 176 178 181 182 189 284 89 92 289 138 147 149 230 278 288 287 327 109 290 0\n371 63 -60 -79 -70 5 30 41 40 32 -58 -53 -8 -48 0 347 346 345 351 92 89 189 183 182 181 180 179 178 177 176 80 77 75 74 73 52 3 42 207 289 138 147 149 230 278 288 287 324 109 290 0\n372 -79 5 30 41 40 32 1 -58 50 52 67 -53 -8 -48 0 343 353 345 351 346 370 80 52 173 176 177 178 179 180 181 183 189 284 92 371 103 110 139 202 287 150 279 290 20 236 288 326 0\n373 -74 -44 -27 -54 -60 -69 -70 32 -58 67 -53 -8 -48 42 0 347 141 116 77 74 42 89 158 289 109 39 234 275 325 0\n374 -54 -60 -69 79 -70 41 40 32 -58 67 -53 -8 -48 42 0 347 351 345 89 156 141 126 118 117 116 77 74 52 42 109 158 280 289 186 290 373 269 287 276 323 0\n375 -69 30 32 1 -58 50 52 67 -53 -8 -48 42 0 353 343 346 347 351 345 39 74 199 52 200 196 372 370 80 77 3 45 44 42 113 115 116 117 118 126 141 156 284 89 92 374 201 288 93 185 235 289 160 290 150 231 287 312 0\n376 -44 61 54 41 32 57 0 346 20 93 288 0\n377 -71 -60 -12 -78 64 -70 5 30 41 40 32 -58 -53 -8 -48 0 347 346 345 80 165 166 376 89 188 171 168 77 74 3 45 44 42 125 289 138 147 230 237 288 287 311 0\n378 56 4 -48 42 0 353 352 343 351 346 217 3 41 40 39 38 369 256 268 213 212 52 355 73 74 75 76 77 78 80 190 193 199 200 191 196 370 372 375 357 291 164 165 166 169 170 266 284 376 377 290 153 154 288 0\n379 -76 -72 29 -78 -67 -56 -8 -48 0 345 346 347 343 169 108 105 168 274 132 107 287 147 146 142 188 171 166 165 164 163 162 3 45 44 42 153 154 238 288 71 289 89 228 284 321 0\n380 -78 4 -48 42 0 349 353 345 350 351 347 41 378 69 285 108 107 105 123 217 42 39 38 162 165 166 168 169 170 171 188 287 142 145 146 147 195 198 197 194 286 132 135 379 290 84 376 289 71 0\n381 -57 78 70 34 0 350 352 70 72 175 286 291 133 0\n382 60 -45 -27 -68 -55 30 -72 61 40 -67 -56 -8 -48 0 347 345 343 87 61 132 128 42 107 108 98 287 147 160 289 63 62 270 284 271 313 0\n383 79 37 61 76 40 41 4 -48 42 0 349 353 350 352 345 351 346 347 378 67 38 123 286 127 191 217 3 41 192 135 133 132 128 380 381 69 285 108 107 105 42 39 291 60 61 87 94 98 287 147 150 290 109 160 281 288 289 382 232 265 315 0\n384 -60 -68 -45 44 -28 -79 -72 4 -48 42 0 345 349 353 347 41 378 69 285 107 108 178 287 147 189 182 176 174 132 128 217 42 39 89 232 272 289 316 0\n385 54 37 61 76 40 41 4 -48 42 0 350 345 349 353 346 351 343 347 41 378 69 285 107 108 383 178 287 150 147 380 189 279 182 176 174 173 172 67 38 123 286 127 191 217 3 192 135 132 128 381 105 79 42 376 288 290 384 270 284 49 264 289 314 0\n386 37 61 76 40 41 4 -48 42 0 349 353 350 345 347 343 41 378 69 285 108 107 123 67 42 38 286 127 128 132 191 383 172 173 178 182 189 287 147 385 57 58 289 284 89 0\n387 -37 70 -8 0 6 131 242 0\n388 -79 -61 30 63 29 66 64 39 0 343 345 347 184 92 91 90 172 178 182 284 287 49 147 289 0\n389 76 -48 4 42 0 349 350 353 352 351 345 347 217 3 378 123 387 38 41 286 127 192 39 67 190 128 200 69 285 105 199 191 135 133 132 108 107 380 42 386 91 148 184 388 291 60 61 98 290 287 160 147 289 0\n390 -48 4 42 0 349 350 353 352 347 345 346 343 38 39 41 42 44 45 217 378 380 3 67 69 123 381 285 387 105 107 108 286 127 128 132 133 190 192 191 200 196 389 153 154 155 157 181 187 238 291 61 62 63 87 98 289 287 274 158 288 92 229 284 322 0\n391 -55 -77 -20 -74 -61 -76 37 48 42 0 343 342 353 349 341 350 144 143 142 92 90 152 367 33 8 62 78 229 284 283 233 55 214 66 68 123 285 208 282 286 329 0\n392 -34 -10 4 0 353 3 24 215 0\n393 -61 -76 37 4 42 0 352 342 341 350 343 353 349 347 345 187 181 157 156 155 152 151 390 367 392 33 8 90 91 92 166 291 62 78 283 66 68 123 205 282 286 22 132 61 206 59 97 98 284 69 204 47 285 289 108 203 287 391 0\n394 -55 61 80 73 62 45 36 41 37 48 42 0 342 341 353 349 350 347 346 367 33 8 61 72 78 87 283 66 68 69 123 206 282 285 286 27 105 132 289 288 158 0\n395 -76 -46 55 4 42 0 352 346 342 353 349 350 345 347 343 30 28 27 26 25 23 21 390 367 392 8 154 155 156 157 181 187 393 291 357 162 163 164 165 168 171 356 209 225 227 193 288 71 80 283 69 123 285 286 108 132 274 287 289 89 228 284 328 0\n396 -78 31 71 40 76 44 0 351 169 170 290 0\n397 -67 -72 -59 61 76 -46 55 34 38 48 4 0 352 343 346 135 134 133 95 89 86 83 30 29 28 26 25 21 104 105 192 191 396 381 291 172 356 284 227 58 288 0\n398 -53 -59 -46 4 0 343 89 86 26 25 21 50 54 55 191 284 0\n399 -59 61 -46 55 4 42 0 353 349 350 395 26 390 367 392 8 398 285 124 397 286 0\n400 -77 49 61 -46 55 4 42 0 352 350 342 353 349 346 351 343 345 395 30 29 28 27 26 25 23 21 390 367 392 8 158 159 160 161 171 182 291 112 114 115 117 118 133 356 286 209 225 226 227 123 124 190 193 192 283 285 288 290 55 201 150 231 284 287 319 0\n401 -73 49 61 -46 55 4 42 0 345 353 349 351 350 352 343 346 395 30 29 28 26 390 367 392 8 137 140 141 147 149 357 287 100 101 102 108 111 285 54 55 69 355 356 80 226 249 290 135 180 286 291 164 165 266 284 288 318 0\n402 -63 -46 55 4 42 0 350 345 353 349 351 395 29 26 390 367 392 8 99 103 110 116 125 132 357 286 287 124 145 150 285 290 52 0\n403 -79 -53 59 -46 4 42 0 343 347 69 355 78 402 77 25 21 26 50 191 55 54 27 23 173 182 189 284 289 92 401 0\n404 71 -53 59 -46 4 42 0 352 343 347 346 351 403 69 355 78 402 395 390 28 367 8 54 356 227 226 80 77 25 21 26 50 191 392 193 55 52 30 29 27 23 396 291 115 141 284 92 400 289 185 186 288 290 109 0\n405 -53 59 -46 4 42 0 352 347 27 23 390 367 392 69 355 77 78 402 403 404 126 161 291 166 188 401 289 0\n406 -77 55 69 34 0 352 171 182 291 0\n407 -73 -67 0 345 108 107 140 147 287 0\n408 -65 55 69 34 0 352 168 178 291 0\n409 -49 61 62 41 32 45 0 346 57 71 288 0\n410 55 59 -46 4 42 0 350 349 353 345 352 347 390 367 8 405 285 407 26 124 286 135 133 132 25 21 104 191 392 192 108 107 105 30 29 27 23 395 406 408 287 145 146 396 291 176 388 409 189 289 0\n411 80 59 -46 4 42 0 350 345 349 353 347 351 390 367 8 405 285 107 108 410 98 287 150 28 62 356 227 226 94 61 407 26 124 286 135 132 392 21 104 192 30 29 27 25 23 289 394 160 393 290 0\n412 59 -46 4 42 0 353 349 350 345 346 351 30 29 28 26 21 390 367 392 8 405 285 104 105 107 108 124 192 286 135 410 62 72 94 98 356 287 226 227 150 411 184 187 288 290 109 0\n413 -46 4 42 0 412 87 91 399 0\n414 -70 46 47 48 0 341 121 122 282 0\n415 -54 78 -59 46 34 47 48 0 350 341 352 343 89 87 86 414 56 58 286 129 133 282 291 13 172 284 0\n416 -32 -59 0 343 89 86 1 2 48 102 105 263 284 0\n417 41 -59 45 71 57 31 46 34 47 48 0 346 416 96 95 91 85 83 82 81 288 362 415 0\n418 4 42 0 351 345 347 352 342 341 350 353 390 367 8 33 392 413 215 414 387 286 127 129 133 282 130 68 210 283 192 80 135 19 16 128 132 14 15 18 193 77 78 362 417 406 357 408 291 181 189 289 147 149 287 290 111 0\n419 -10 -4 0 119 64 31 220 218 241 243 244 239 332 0\n420 42 0 418 31 64 119 419 367 45 219 241 243 244 239 332 0\n421 -9 0 420 10 0\n422 -38 0 420 12 0\n423 -43 0 420 17 0\n424 -48 0 420 43 0\n425 -50 0 420 46 0\n426 0 421 425 422 423 424 356 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.l) :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 3
 (.leaf (⟨2, by decide⟩))
 (.branch 4
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨4, by decide⟩)))))
 (.branch 7
 (.branch 6
 (.leaf (⟨5, by decide⟩))
 (.leaf (⟨6, by decide⟩)))
 (.branch 8
 (.leaf (⟨7, by decide⟩))
 (.branch 9
 (.leaf (⟨8, by decide⟩))
 (.leaf (⟨9, by decide⟩))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 13
 (.leaf (⟨2, by decide⟩))
 (.branch 14
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨4, by decide⟩)))))
 (.branch 17
 (.branch 16
 (.leaf (⟨5, by decide⟩))
 (.leaf (⟨6, by decide⟩)))
 (.branch 18
 (.leaf (⟨7, by decide⟩))
 (.branch 19
 (.leaf (⟨8, by decide⟩))
 (.leaf (⟨9, by decide⟩)))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.g)) :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([]))
 (.leaf ([])))
 (.branch 3
 (.leaf ([]))
 (.branch 4
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 7
 (.branch 6
 (.leaf ([]))
 (.leaf ([])))
 (.branch 8
 (.leaf ([]))
 (.branch 9
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 13
 (.leaf ([⟨1, by decide⟩]))
 (.branch 14
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 17
 (.branch 16
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 18
 (.leaf ([⟨1, by decide⟩]))
 (.branch 19
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9aa5a698e62da4e2ba1e4789e1783e9a659694e52d64d2b61d4749d1743d68e6338f13a4e532ce2b2ad1b26c5b0ee4751cc749e1715c3783d0f23d941b1929286a8698629866458961382e07991924698658529465454951342d0758390ca318e1344c9382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492449249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 67), (facetIndex 72), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 71), (facetIndex 73), (facetIndex 74), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 83), (facetIndex 85), (facetIndex 86), (facetIndex 87)]))
 (.branch 4
 (.leaf ([(facetIndex 47), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 64)]))
 (.leaf ([(facetIndex 48), (facetIndex 55), (facetIndex 56), (facetIndex 60), (facetIndex 61), (facetIndex 62)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 69), (facetIndex 70)]))
 (.branch 7
 (.leaf ([(facetIndex 79), (facetIndex 84), (facetIndex 88), (facetIndex 89)]))
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 63), (facetIndex 65)]))))
 (.branch 9
 (.leaf ([(facetIndex 78), (facetIndex 80), (facetIndex 81), (facetIndex 82)]))
 (.branch 10
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 53), (facetIndex 58)]))
 (.leaf ([(facetIndex 46), (facetIndex 49)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6622262888680011101555057374447974409333a43a999z2b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6, 7]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [6, 7]
def grouped2_0015 : List Nat := [7]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9, 10]
def grouped2_0018 : List Nat := [9]
def grouped2_0019 : List Nat := [9, 10]
def grouped2_0020 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0014\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record012" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record012" "{\"ridges\":[[21,21],[25,25],[30,14],[30,42],[43,14],[44,259],[44,261],[46,35],[49,35],[53,25],[53,26],[53,42],[58,35],[58,42],[59,35],[60,529],[62,259],[64,35],[65,35],[65,259],[69,25],[70,21],[73,21],[77,41],[81,14],[81,26],[83,14],[84,14],[88,26],[89,42]],\"owners\":[[81,14,[0,30,31,43,45,83,84],[29,44,80,82]],[44,261,[21,24,75],[5,49,51,69]],[77,41,[7,18,53,57,66,71],[26,58]],[53,42,[30,38,83,89],[7,57,58,78]],[58,42,[30,38,78,83],[7,53,57,89]],[60,529,[25,70],[12,48,61,62,76]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-12,-2],[-13,-10],[-13,-11],[-13,-12],[-14,-10],[-14,-11],[-14,-12],[-14,-13],[-15,-11],[-16,-14],[-17,-10],[-17,-11],[-17,-12],[-17,-13],[-17,-16],[-18,-10],[-18,-11],[-18,-12],[-18,-13],[-18,-16],[-19,-10],[-19,-11],[-19,-12],[-19,-13],[-19,-16],[-20,-1],[-20,-13],[-20,-15],[-21,-12],[-23,-11],[-23,-20],[-24,-10],[-24,-12],[-24,-13],[-24,-16],[-24,-20],[-25,-21],[-25,-24],[-26,-10],[-26,-13],[-26,-15],[-26,-17],[-26,-20],[-26,-22],[-26,-23],[-28,-26],[-29,-20],[-29,-26],[-30,-13],[-30,-16],[-30,-17],[-30,-20],[-30,-25],[-31,-24],[-31,-25],[-31,-27],[-31,-30],[-32,-10],[-32,-16],[-32,-17],[-32,-22],[-32,-24],[-32,-28],[-33,-26],[-35,-34],[-36,-34],[-37,-12],[-37,-20],[-37,-21],[-37,-34],[-38,-13],[-38,-16],[-38,-33],[-38,-34],[-38,-35],[-39,-12],[-39,-37],[-40,-5],[-40,-13],[-40,-20],[-40,-26],[-40,-33],[-40,-35],[-40,-36],[-41,-3],[-41,-13],[-41,-16],[-41,-33],[-42,-16],[-42,-32],[-43,-12],[-43,-25],[-43,-37],[-44,-25],[-45,-11],[-45,-20],[-46,-45],[-47,-13],[-47,-38],[-47,-46],[-48,-11],[-48,-36],[-48,-46],[-49,-20],[-49,-46],[-50,-16],[-50,-35],[-50,-38],[-50,-47],[-51,-9],[-51,-12],[-51,-37],[-51,-39],[-51,-45],[-51,-49],[-52,-20],[-52,-40],[-52,-47],[-53,-16],[-53,-41],[-54,-16],[-54,-32],[-54,-47],[-55,-12],[-55,-25],[-55,-49],[-56,-8],[-56,-25],[-56,-31],[-48,1,7,8,10,12,50,51],[-7,-48,-51],[-10,-48,-51],[-48,-50,-51],[-4,-37,-40],[-13,-25,-32],[-16,-26,-31],[-11,-29,-32],[-11,4,5,42],[-6,-20,-36],[-20,-48,-55],[-44,2,3,20,24,33,38],[-20,7,9,50,56],[-25,7,9,45,50],[-7,-20,-56],[-27,6,37],[-57,21,34,39,43,44],[-58,38,40,41,42],[-59,50,52,53,54],[-60,14,17,18,19,31],[-61,15,22,23,27,28,29],[-62,33,35,36,37],[-63,46,51,55,56],[-64,24,26,30,32],[-65,45,47,48,49],[-66,10,11,12,20,25],[-67,13,16],[-68,57],[-68,58],[-69,60],[-69,61],[-70,59],[-70,69],[-71,68,70],[-72,68],[-72,70],[-73,63],[-73,64],[-74,62],[-74,73],[-75,66,67],[-76,66],[-76,67],[-77,65,76],[-78,65],[-77,75],[-78,76],[-79,74,78],[-80,74],[-79,77],[-80,78],[-81,71],[-81,72,80],[-81,79],[81]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":7},{\"tag\":\"incompatible\",\"a\":46,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":43},{\"tag\":\"incompatible\",\"a\":51,\"b\":44},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":43},{\"tag\":\"incompatible\",\"a\":52,\"b\":44},{\"tag\":\"incompatible\",\"a\":52,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":0},{\"tag\":\"incompatible\",\"a\":53,\"b\":46},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":43},{\"tag\":\"incompatible\",\"a\":57,\"b\":45},{\"tag\":\"incompatible\",\"a\":57,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":46},{\"tag\":\"incompatible\",\"a\":59,\"b\":48},{\"tag\":\"incompatible\",\"a\":59,\"b\":50},{\"tag\":\"incompatible\",\"a\":59,\"b\":53},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":46},{\"tag\":\"incompatible\",\"a\":63,\"b\":49},{\"tag\":\"incompatible\",\"a\":63,\"b\":50},{\"tag\":\"incompatible\",\"a\":63,\"b\":53},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":49},{\"tag\":\"incompatible\",\"a\":65,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":55},{\"tag\":\"incompatible\",\"a\":65,\"b\":57},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":45},{\"tag\":\"incompatible\",\"a\":70,\"b\":53},{\"tag\":\"incompatible\",\"a\":70,\"b\":54},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":46},{\"tag\":\"incompatible\",\"a\":71,\"b\":49},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":72,\"b\":45},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":24},{\"tag\":\"incompatible\",\"a\":73,\"b\":46},{\"tag\":\"incompatible\",\"a\":73,\"b\":53},{\"tag\":\"incompatible\",\"a\":73,\"b\":59},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":18},{\"tag\":\"incompatible\",\"a\":74,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":49},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":75,\"b\":49},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":76,\"b\":45},{\"tag\":\"incompatible\",\"a\":76,\"b\":58},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":58},{\"tag\":\"incompatible\",\"a\":78,\"b\":44},{\"tag\":\"incompatible\",\"a\":78,\"b\":53},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":46},{\"tag\":\"incompatible\",\"a\":80,\"b\":71},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":44},{\"tag\":\"incompatible\",\"a\":81,\"b\":69},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":53},{\"tag\":\"incompatible\",\"a\":82,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":49},{\"tag\":\"incompatible\",\"a\":83,\"b\":68},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":83,\"b\":80},{\"tag\":\"incompatible\",\"a\":84,\"b\":38},{\"tag\":\"incompatible\",\"a\":84,\"b\":45},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":72},{\"tag\":\"incompatible\",\"a\":84,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":53},{\"tag\":\"incompatible\",\"a\":85,\"b\":73},{\"tag\":\"incompatible\",\"a\":85,\"b\":80},{\"tag\":\"incompatible\",\"a\":86,\"b\":49},{\"tag\":\"incompatible\",\"a\":86,\"b\":74},{\"tag\":\"incompatible\",\"a\":87,\"b\":49},{\"tag\":\"incompatible\",\"a\":87,\"b\":65},{\"tag\":\"incompatible\",\"a\":87,\"b\":80},{\"tag\":\"incompatible\",\"a\":88,\"b\":45},{\"tag\":\"incompatible\",\"a\":88,\"b\":58},{\"tag\":\"incompatible\",\"a\":88,\"b\":82},{\"tag\":\"incompatible\",\"a\":89,\"b\":31},{\"tag\":\"incompatible\",\"a\":89,\"b\":58},{\"tag\":\"incompatible\",\"a\":89,\"b\":64},{\"tag\":\"mate\",\"ridge\":14,\"a\":81,\"owners\":[0,30,31,43,45,83,84]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[30,81,84]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[43,81,84]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[81,83,84]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[21,70,73]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[46,58,65]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[49,59,64]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[44,62,65]},{\"tag\":\"mate\",\"ridge\":261,\"a\":44,\"owners\":[21,24,75]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[25,53,69]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[53,81,88]},{\"tag\":\"mate\",\"ridge\":41,\"a\":77,\"owners\":[7,18,53,57,66,71]},{\"tag\":\"mate\",\"ridge\":42,\"a\":53,\"owners\":[30,38,83,89]},{\"tag\":\"mate\",\"ridge\":42,\"a\":58,\"owners\":[30,38,78,83]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[30,53,89]},{\"tag\":\"mate\",\"ridge\":529,\"a\":60,\"owners\":[25,70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[54,67,72,76,77],\"full_literals\":[-57,21,34,39,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[71,73,74,75],\"full_literals\":[-58,38,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[83,85,86,87],\"full_literals\":[-59,50,52,53,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[47,50,51,52,64],\"full_literals\":[-60,14,17,18,19,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[48,55,56,60,61,62],\"full_literals\":[-61,15,22,23,27,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[66,68,69,70],\"full_literals\":[-62,33,35,36,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[79,84,88,89],\"full_literals\":[-63,46,51,55,56]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[57,59,63,65],\"full_literals\":[-64,24,26,30,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[78,80,81,82],\"full_literals\":[-65,45,47,48,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[43,44,45,53,58],\"full_literals\":[-66,10,11,12,20,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[46,49],\"full_literals\":[-67,13,16]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-70,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,68,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-72,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-74,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,66,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,65,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-78,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-79,74,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-80,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-80,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":6,\"direction\":\"backward\",\"full_literals\":[-81,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-81,72,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-81,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "p cnf 81 184\n-12 -2 0\n-13 -10 0\n-13 -11 0\n-13 -12 0\n-14 -10 0\n-14 -11 0\n-14 -12 0\n-14 -13 0\n-15 -11 0\n-16 -14 0\n-17 -10 0\n-17 -11 0\n-17 -12 0\n-17 -13 0\n-17 -16 0\n-18 -10 0\n-18 -11 0\n-18 -12 0\n-18 -13 0\n-18 -16 0\n-19 -10 0\n-19 -11 0\n-19 -12 0\n-19 -13 0\n-19 -16 0\n-20 -1 0\n-20 -13 0\n-20 -15 0\n-21 -12 0\n-23 -11 0\n-23 -20 0\n-24 -10 0\n-24 -12 0\n-24 -13 0\n-24 -16 0\n-24 -20 0\n-25 -21 0\n-25 -24 0\n-26 -10 0\n-26 -13 0\n-26 -15 0\n-26 -17 0\n-26 -20 0\n-26 -22 0\n-26 -23 0\n-28 -26 0\n-29 -20 0\n-29 -26 0\n-30 -13 0\n-30 -16 0\n-30 -17 0\n-30 -20 0\n-30 -25 0\n-31 -24 0\n-31 -25 0\n-31 -27 0\n-31 -30 0\n-32 -10 0\n-32 -16 0\n-32 -17 0\n-32 -22 0\n-32 -24 0\n-32 -28 0\n-33 -26 0\n-35 -34 0\n-36 -34 0\n-37 -12 0\n-37 -20 0\n-37 -21 0\n-37 -34 0\n-38 -13 0\n-38 -16 0\n-38 -33 0\n-38 -34 0\n-38 -35 0\n-39 -12 0\n-39 -37 0\n-40 -5 0\n-40 -13 0\n-40 -20 0\n-40 -26 0\n-40 -33 0\n-40 -35 0\n-40 -36 0\n-41 -3 0\n-41 -13 0\n-41 -16 0\n-41 -33 0\n-42 -16 0\n-42 -32 0\n-43 -12 0\n-43 -25 0\n-43 -37 0\n-44 -25 0\n-45 -11 0\n-45 -20 0\n-46 -45 0\n-47 -13 0\n-47 -38 0\n-47 -46 0\n-48 -11 0\n-48 -36 0\n-48 -46 0\n-49 -20 0\n-49 -46 0\n-50 -16 0\n-50 -35 0\n-50 -38 0\n-50 -47 0\n-51 -9 0\n-51 -12 0\n-51 -37 0\n-51 -39 0\n-51 -45 0\n-51 -49 0\n-52 -20 0\n-52 -40 0\n-52 -47 0\n-53 -16 0\n-53 -41 0\n-54 -16 0\n-54 -32 0\n-54 -47 0\n-55 -12 0\n-55 -25 0\n-55 -49 0\n-56 -8 0\n-56 -25 0\n-56 -31 0\n-48 1 7 8 10 12 50 51 0\n-7 -48 -51 0\n-10 -48 -51 0\n-48 -50 -51 0\n-4 -37 -40 0\n-13 -25 -32 0\n-16 -26 -31 0\n-11 -29 -32 0\n-11 4 5 42 0\n-6 -20 -36 0\n-20 -48 -55 0\n-44 2 3 20 24 33 38 0\n-20 7 9 50 56 0\n-25 7 9 45 50 0\n-7 -20 -56 0\n-27 6 37 0\n-57 21 34 39 43 44 0\n-58 38 40 41 42 0\n-59 50 52 53 54 0\n-60 14 17 18 19 31 0\n-61 15 22 23 27 28 29 0\n-62 33 35 36 37 0\n-63 46 51 55 56 0\n-64 24 26 30 32 0\n-65 45 47 48 49 0\n-66 10 11 12 20 25 0\n-67 13 16 0\n-68 57 0\n-68 58 0\n-69 60 0\n-69 61 0\n-70 59 0\n-70 69 0\n-71 68 70 0\n-72 68 0\n-72 70 0\n-73 63 0\n-73 64 0\n-74 62 0\n-74 73 0\n-75 66 67 0\n-76 66 0\n-76 67 0\n-77 65 76 0\n-78 65 0\n-77 75 0\n-78 76 0\n-79 74 78 0\n-80 74 0\n-79 77 0\n-80 78 0\n-81 71 0\n-81 72 80 0\n-81 79 0\n81 0\n"
  "185 71 0 184 181 0\n186 79 0 184 183 0\n187 77 0 186 179 0\n188 75 0 187 175 0\n189 -46 -65 0 97 100 103 105 154 0\n190 -47 -59 -67 0 98 109 118 123 156 148 119 0\n191 -51 56 12 47 -78 0 176 171 174 110 114 115 154 101 131 132 133 142 143 155 0\n192 56 55 12 47 -80 0 180 174 189 178 169 166 191 152 0\n193 -13 12 25 -66 0 2 3 27 155 0\n194 -16 31 -60 0 10 15 20 25 149 0\n195 -56 -60 -76 0 172 171 128 129 194 156 4 193 0\n196 -13 -70 -80 0 180 176 162 159 195 172 161 190 171 4 193 192 125 0\n197 -70 -80 0 180 176 172 178 169 167 162 159 196 156 35 50 59 194 153 136 0\n198 -16 -80 0 185 197 163 158 178 169 167 35 50 59 72 87 89 153 147 81 0\n199 -80 0 178 180 169 176 167 171 172 198 156 4 34 40 49 193 153 135 0\n200 72 0 199 184 182 0\n201 68 0 200 164 0\n202 70 0 200 165 0\n203 57 0 201 157 0\n204 58 0 201 158 0\n205 59 0 202 161 0\n206 69 0 202 162 0\n207 60 0 206 159 0\n208 61 0 206 160 0\n209 -25 56 -63 46 34 0 203 37 92 94 125 146 152 113 0\n210 -51 -62 -65 47 35 33 0 112 114 115 151 154 102 0\n211 -48 -55 25 -66 10 0 124 101 140 155 0\n212 56 51 -63 -65 -66 47 34 10 0 189 209 152 124 126 211 154 95 96 155 0\n213 -11 31 17 0 207 6 17 22 149 0\n214 -20 48 -65 47 0 96 104 154 0\n215 -12 31 17 0 207 7 18 23 149 0\n216 31 -56 51 -65 -66 50 47 -32 0 128 127 60 58 213 215 155 26 144 214 130 0\n217 -56 51 -32 -65 -66 50 47 0 216 129 0\n218 -38 -32 16 0 188 187 186 58 71 73 74 75 99 108 156 172 170 176 173 177 168 169 166 210 212 217 0\n219 -40 -32 16 0 188 186 203 90 58 78 79 80 82 83 84 156 172 170 176 177 168 151 67 69 70 77 93 134 146 138 94 155 0\n220 -11 -32 0 208 63 61 60 9 30 137 213 150 56 0\n221 -20 35 -62 33 28 22 0 208 28 31 47 68 150 151 145 139 0\n222 -12 20 34 33 3 38 24 0 203 1 29 76 91 141 146 0\n223 -25 34 76 0 187 186 176 177 169 166 173 189 128 209 0\n224 -20 -62 53 33 54 28 22 0 205 116 221 148 107 0\n225 34 20 11 -66 76 33 3 38 24 10 0 223 222 155 0\n226 -32 16 0 204 188 186 58 61 62 63 90 122 218 219 147 85 86 88 120 156 172 170 176 177 168 220 224 225 65 66 70 151 0\n227 -34 33 -62 0 65 66 70 151 0\n228 76 34 11 20 10 -66 0 187 186 176 173 223 177 189 155 169 13 111 124 215 166 152 129 0\n229 -13 -64 32 0 34 40 49 153 0\n230 -26 20 10 -66 76 0 186 208 176 177 168 41 42 44 45 46 48 64 150 227 56 228 213 0\n231 -30 20 10 -66 0 51 53 57 213 215 155 0\n232 20 10 -66 76 -64 32 0 230 231 153 33 38 54 155 12 213 0\n233 -20 -64 32 0 36 43 52 153 0\n234 -10 -64 32 0 207 5 11 16 21 32 39 149 153 57 0\n235 -64 16 0 188 226 229 156 172 233 234 170 232 0\n236 16 0 186 207 235 167 169 177 176 171 172 156 4 8 14 19 24 193 149 55 0\n237 -38 0 236 72 0\n238 -41 0 236 87 0\n239 -42 0 236 89 0\n240 -50 0 236 106 0\n241 -53 0 236 119 0\n242 -54 0 236 121 0\n243 40 0 239 238 204 237 147 0\n244 52 0 242 241 240 205 148 0\n245 0 244 243 117 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "969a665a56559362d87663a4e3386e1783e965a565655555352d4756364d3346d1743d68f1364d538cd332cc73a2d8b32e2b1ae1b16c3b91d4731d2719e1725e0f43c1f2b252928aa618a6458560d88e1382e946492a58529515154352344d0b58390ca384d1314c3382c8b12c2b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 69), (facetIndex 71), (facetIndex 78)]))
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57)])))
 (.branch 3
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64)]))
 (.branch 4
 (.leaf ([(facetIndex 40), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 66), (facetIndex 67), (facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 93)]))
 (.leaf ([(facetIndex 83), (facetIndex 85), (facetIndex 92)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 48), (facetIndex 75), (facetIndex 89)]))
 (.leaf ([(facetIndex 49), (facetIndex 70), (facetIndex 76), (facetIndex 84), (facetIndex 90)])))
 (.branch 8
 (.leaf ([(facetIndex 46), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 91)]))
 (.branch 9
 (.leaf ([(facetIndex 45), (facetIndex 68), (facetIndex 72), (facetIndex 82), (facetIndex 86)]))
 (.leaf ([(facetIndex 65), (facetIndex 74), (facetIndex 88)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "347659784648333076597806083392222222111113336507822113z28;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record013" 73

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record013" "{\"ridges\":[[16,385],[22,273],[24,133],[24,261],[24,385],[28,44],[33,274],[35,388],[39,140],[45,35],[45,38],[48,261],[54,35],[65,35],[65,385],[69,133],[69,140],[71,261],[71,385],[72,49],[73,133],[73,164],[74,261],[74,273],[75,273],[77,273],[77,385],[78,385],[85,140],[85,386],[85,388],[86,50],[88,274],[89,84],[89,274],[91,274],[91,388],[92,386]],\"owners\":[[45,38,[28,31,34,88,92],[2,46,82,86]],[72,49,[10,50,59,60,61],[20,58,66,73,74]],[86,50,[10,50,59,60,61],[31,58,80,87,88]],[22,273,[12,60,62,63,64],[74,75,77]],[74,273,[12,62,63,64],[22,60,75,77]],[75,273,[12,60,63,64],[22,62,74,77]],[77,273,[12,60,62,64],[22,63,74,75]],[33,274,[12,60,62,63,64],[88,89,91]],[88,274,[12,62,63,64],[33,60,89,91]],[89,274,[12,60,63,64],[33,62,88,91]],[91,274,[12,60,62,64],[33,63,88,89]],[16,385,[24,71,77,78],[56,63,65]],[24,385,[16,56,63,65],[71,77,78]],[65,385,[24,71,77],[16,56,63,78]],[71,385,[16,63,65],[24,56,77,78]],[77,385,[16,56,65],[24,63,71,78]],[78,385,[16,56,63],[24,65,71,77]],[85,386,[16,63,65],[35,56,91,92]],[92,386,[16,56,63],[35,65,85,91]],[28,44,[17,39,66,68],[80,82]],[89,84,[21,67,72,76],[32,75,81,86,90]],[73,164,[34,39,92],[23,78,87]],[35,388,[24,71,77,78],[85,91,92]],[85,388,[24,77,78],[35,71,91,92]],[91,388,[24,71,78],[35,77,85,92]]],\"edges\":[[33,[12,22,33,60,62,63,64,74,75,77,88,89,91]],[42,[16,24,35,56,63,65,71,77,78,85,91,92]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-1],[-20,-14],[-22,-15],[-23,-18],[-23,-22],[-24,-22],[-25,-22],[-27,-22],[-28,-1],[-29,-19],[-30,-1],[-31,-2],[-31,-30],[-32,-1],[-32,-31],[-33,-19],[-34,-1],[-34,-31],[-35,-3],[-35,-16],[-35,-19],[-35,-20],[-35,-25],[-35,-26],[-35,-27],[-35,-30],[-39,-4],[-39,-14],[-39,-36],[-39,-37],[-39,-38],[-40,-14],[-40,-16],[-40,-20],[-40,-26],[-40,-38],[-42,-29],[-42,-33],[-42,-40],[-43,-5],[-43,-37],[-43,-41],[-44,-43],[-45,-43],[-46,-16],[-46,-21],[-46,-29],[-46,-33],[-46,-43],[-46,-44],[-47,-43],[-49,-15],[-49,-20],[-49,-39],[-49,-48],[-50,-11],[-50,-20],[-50,-26],[-50,-40],[-50,-48],[-52,-29],[-52,-33],[-52,-50],[-53,-19],[-53,-35],[-53,-47],[-53,-52],[-54,-9],[-54,-53],[-55,-29],[-55,-33],[-55,-50],[-55,-53],[-56,-20],[-56,-43],[-56,-53],[-18,-24,-35],[-18,8,9,11,53,56],[-7,-39,-42],[-7,-21,-43],[-21,-40,-43],[-41,1,22,29,30,31],[-51,1,22,29,30,31],[-6,2,30,32,33,34],[-43,2,32,33,34],[-44,2,30,33,34],[-46,2,30,32,34],[-10,2,30,32,33,34],[-53,2,32,33,34],[-54,2,30,33,34],[-55,2,30,32,34],[-3,7,40,46,47],[-7,3,26,33,35],[-35,7,40,46],[-40,3,33,35],[-46,3,26,35],[-47,3,26,33],[-50,3,33,35],[-56,3,26,33],[-8,4,13,36,38],[-13,-39,-50],[-54,5,37,41,45],[-42,11,13,56],[-12,7,40,46,47],[-50,7,46,47],[-55,7,40,47],[-57,20,39,40,47],[-58,14,15,23,24,25,26,27],[-59,16,17,28,29,30,31,32,33,34],[-60,49,50,56],[-61,21,44,54],[-62,19,42,46,52,55],[-63,18,38,41,48,51],[-64,35,43,53],[-65,57],[-65,58],[-66,60],[-67,59],[-67,66],[-68,65],[-68,67],[-69,61],[-70,63],[-70,64],[-71,62],[-71,70],[-72,69],[-72,71],[-73,68],[-73,72],[73],[2,6,10,30,32,33,34,43,44,46,53,54,55],[3,7,12,26,33,35,40,46,47,50,55,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":10},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":54,\"b\":50},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":58,\"b\":10},{\"tag\":\"incompatible\",\"a\":59,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":10},{\"tag\":\"incompatible\",\"a\":61,\"b\":12},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":10},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":46},{\"tag\":\"incompatible\",\"a\":64,\"b\":10},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":16},{\"tag\":\"incompatible\",\"a\":65,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":46},{\"tag\":\"incompatible\",\"a\":65,\"b\":47},{\"tag\":\"incompatible\",\"a\":65,\"b\":55},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":57},{\"tag\":\"incompatible\",\"a\":65,\"b\":60},{\"tag\":\"incompatible\",\"a\":69,\"b\":17},{\"tag\":\"incompatible\",\"a\":69,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":41},{\"tag\":\"incompatible\",\"a\":71,\"b\":43},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":56},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":59},{\"tag\":\"incompatible\",\"a\":73,\"b\":63},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":21},{\"tag\":\"incompatible\",\"a\":74,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":43},{\"tag\":\"incompatible\",\"a\":77,\"b\":48},{\"tag\":\"incompatible\",\"a\":77,\"b\":59},{\"tag\":\"incompatible\",\"a\":77,\"b\":63},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":42},{\"tag\":\"incompatible\",\"a\":83,\"b\":47},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":34},{\"tag\":\"incompatible\",\"a\":85,\"b\":47},{\"tag\":\"incompatible\",\"a\":85,\"b\":56},{\"tag\":\"incompatible\",\"a\":85,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":87,\"b\":59},{\"tag\":\"incompatible\",\"a\":87,\"b\":63},{\"tag\":\"incompatible\",\"a\":87,\"b\":85},{\"tag\":\"incompatible\",\"a\":88,\"b\":46},{\"tag\":\"incompatible\",\"a\":88,\"b\":65},{\"tag\":\"incompatible\",\"a\":88,\"b\":78},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":31},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":59},{\"tag\":\"incompatible\",\"a\":91,\"b\":63},{\"tag\":\"incompatible\",\"a\":91,\"b\":85},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":47},{\"tag\":\"incompatible\",\"a\":92,\"b\":74},{\"tag\":\"incompatible\",\"a\":92,\"b\":88},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[45,54,65]},{\"tag\":\"mate\",\"ridge\":38,\"a\":45,\"owners\":[28,31,34,88,92]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[24,69,73]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[24,48,74]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[48,71,74]},{\"tag\":\"mate\",\"ridge\":49,\"a\":72,\"owners\":[10,50,59,60,61]},{\"tag\":\"mate\",\"ridge\":50,\"a\":86,\"owners\":[10,50,59,60,61]},{\"tag\":\"mate\",\"ridge\":273,\"a\":22,\"owners\":[12,60,62,63,64]},{\"tag\":\"mate\",\"ridge\":273,\"a\":74,\"owners\":[12,62,63,64]},{\"tag\":\"mate\",\"ridge\":273,\"a\":75,\"owners\":[12,60,63,64]},{\"tag\":\"mate\",\"ridge\":273,\"a\":77,\"owners\":[12,60,62,64]},{\"tag\":\"mate\",\"ridge\":274,\"a\":33,\"owners\":[12,60,62,63,64]},{\"tag\":\"mate\",\"ridge\":274,\"a\":88,\"owners\":[12,62,63,64]},{\"tag\":\"mate\",\"ridge\":274,\"a\":89,\"owners\":[12,60,63,64]},{\"tag\":\"mate\",\"ridge\":274,\"a\":91,\"owners\":[12,60,62,64]},{\"tag\":\"mate\",\"ridge\":385,\"a\":16,\"owners\":[24,71,77,78]},{\"tag\":\"mate\",\"ridge\":385,\"a\":24,\"owners\":[16,56,63,65]},{\"tag\":\"mate\",\"ridge\":385,\"a\":65,\"owners\":[24,71,77]},{\"tag\":\"mate\",\"ridge\":385,\"a\":71,\"owners\":[16,63,65]},{\"tag\":\"mate\",\"ridge\":385,\"a\":77,\"owners\":[16,56,65]},{\"tag\":\"mate\",\"ridge\":385,\"a\":78,\"owners\":[16,56,63]},{\"tag\":\"mate\",\"ridge\":386,\"a\":85,\"owners\":[16,63,65]},{\"tag\":\"mate\",\"ridge\":386,\"a\":92,\"owners\":[16,56,63]},{\"tag\":\"mate\",\"ridge\":44,\"a\":28,\"owners\":[17,39,66,68]},{\"tag\":\"three\",\"ridge\":140,\"vertices\":[39,69,85]},{\"tag\":\"mate\",\"ridge\":84,\"a\":89,\"owners\":[21,67,72,76]},{\"tag\":\"mate\",\"ridge\":164,\"a\":73,\"owners\":[34,39,92]},{\"tag\":\"mate\",\"ridge\":388,\"a\":35,\"owners\":[24,71,77,78]},{\"tag\":\"mate\",\"ridge\":388,\"a\":85,\"owners\":[24,77,78]},{\"tag\":\"mate\",\"ridge\":388,\"a\":91,\"owners\":[24,71,78]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[47,69,71,78],\"full_literals\":[-57,20,39,40,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[41,42,53,54,55,56,57],\"full_literals\":[-58,14,15,23,24,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[43,44,58,59,60,61,62,63,64],\"full_literals\":[-59,16,17,28,29,30,31,32,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[83,85,92],\"full_literals\":[-60,49,50,56]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[48,75,89],\"full_literals\":[-61,21,44,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[46,73,77,87,91],\"full_literals\":[-62,19,42,46,52,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[45,68,72,82,86],\"full_literals\":[-63,18,38,41,48,51]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[65,74,88],\"full_literals\":[-64,35,43,53]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-68,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-72,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-73,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-73,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[12,22,33,60,62,63,64,74,75,77,88,89,91]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[16,24,35,56,63,65,71,77,78,85,91,92]}]}"
  "p cnf 73 133\n-17 -1 0\n-20 -14 0\n-22 -15 0\n-23 -18 0\n-23 -22 0\n-24 -22 0\n-25 -22 0\n-27 -22 0\n-28 -1 0\n-29 -19 0\n-30 -1 0\n-31 -2 0\n-31 -30 0\n-32 -1 0\n-32 -31 0\n-33 -19 0\n-34 -1 0\n-34 -31 0\n-35 -3 0\n-35 -16 0\n-35 -19 0\n-35 -20 0\n-35 -25 0\n-35 -26 0\n-35 -27 0\n-35 -30 0\n-39 -4 0\n-39 -14 0\n-39 -36 0\n-39 -37 0\n-39 -38 0\n-40 -14 0\n-40 -16 0\n-40 -20 0\n-40 -26 0\n-40 -38 0\n-42 -29 0\n-42 -33 0\n-42 -40 0\n-43 -5 0\n-43 -37 0\n-43 -41 0\n-44 -43 0\n-45 -43 0\n-46 -16 0\n-46 -21 0\n-46 -29 0\n-46 -33 0\n-46 -43 0\n-46 -44 0\n-47 -43 0\n-49 -15 0\n-49 -20 0\n-49 -39 0\n-49 -48 0\n-50 -11 0\n-50 -20 0\n-50 -26 0\n-50 -40 0\n-50 -48 0\n-52 -29 0\n-52 -33 0\n-52 -50 0\n-53 -19 0\n-53 -35 0\n-53 -47 0\n-53 -52 0\n-54 -9 0\n-54 -53 0\n-55 -29 0\n-55 -33 0\n-55 -50 0\n-55 -53 0\n-56 -20 0\n-56 -43 0\n-56 -53 0\n-18 -24 -35 0\n-18 8 9 11 53 56 0\n-7 -39 -42 0\n-7 -21 -43 0\n-21 -40 -43 0\n-41 1 22 29 30 31 0\n-51 1 22 29 30 31 0\n-6 2 30 32 33 34 0\n-43 2 32 33 34 0\n-44 2 30 33 34 0\n-46 2 30 32 34 0\n-10 2 30 32 33 34 0\n-53 2 32 33 34 0\n-54 2 30 33 34 0\n-55 2 30 32 34 0\n-3 7 40 46 47 0\n-7 3 26 33 35 0\n-35 7 40 46 0\n-40 3 33 35 0\n-46 3 26 35 0\n-47 3 26 33 0\n-50 3 33 35 0\n-56 3 26 33 0\n-8 4 13 36 38 0\n-13 -39 -50 0\n-54 5 37 41 45 0\n-42 11 13 56 0\n-12 7 40 46 47 0\n-50 7 46 47 0\n-55 7 40 47 0\n-57 20 39 40 47 0\n-58 14 15 23 24 25 26 27 0\n-59 16 17 28 29 30 31 32 33 34 0\n-60 49 50 56 0\n-61 21 44 54 0\n-62 19 42 46 52 55 0\n-63 18 38 41 48 51 0\n-64 35 43 53 0\n-65 57 0\n-65 58 0\n-66 60 0\n-67 59 0\n-67 66 0\n-68 65 0\n-68 67 0\n-69 61 0\n-70 63 0\n-70 64 0\n-71 62 0\n-71 70 0\n-72 69 0\n-72 71 0\n-73 68 0\n-73 72 0\n73 0\n2 6 10 30 32 33 34 43 44 46 53 54 55 0\n3 7 12 26 33 35 40 46 47 50 55 56 0\n"
  "134 68 0 131 129 0\n135 72 0 131 130 0\n136 65 0 134 120 0\n137 67 0 134 121 0\n138 69 0 135 127 0\n139 71 0 135 128 0\n140 57 0 136 115 0\n141 58 0 136 116 0\n142 59 0 137 118 0\n143 66 0 137 119 0\n144 61 0 138 122 0\n145 62 0 139 125 0\n146 70 0 139 126 0\n147 60 0 143 117 0\n148 63 0 146 123 0\n149 64 0 146 124 0\n150 7 46 33 26 40 3 0 99 97 94 106 105 104 133 0\n151 -46 54 0 144 46 50 111 0\n152 -14 47 40 0 140 2 28 107 0\n153 -33 0 145 16 38 48 62 71 112 0\n154 -39 31 56 3 22 1 29 0 147 153 145 148 27 29 31 54 110 56 60 63 72 98 101 21 26 65 100 103 82 83 112 113 151 78 68 0\n155 31 20 3 14 22 1 29 26 0 140 153 147 148 141 99 97 154 107 36 59 95 110 23 25 26 52 55 82 83 113 4 77 108 0\n156 -31 2 0 153 13 15 18 89 84 86 87 88 90 91 85 132 0\n157 31 3 26 14 22 1 29 0 153 155 22 34 93 96 150 0\n158 -20 0 147 53 57 74 110 0\n159 -47 35 0 149 51 66 114 0\n160 -43 37 -7 0 144 40 42 43 44 80 111 102 0\n161 40 46 -3 0 158 140 149 145 19 159 107 92 30 79 160 114 64 67 73 112 0\n162 -53 42 46 0 145 64 67 73 112 0\n163 46 -3 0 149 144 19 161 39 162 114 40 41 42 43 44 81 111 102 0\n164 -3 0 149 19 163 49 151 114 69 0\n165 -31 0 12 156 0\n166 -14 47 0 32 152 0\n167 -22 26 0 164 153 141 97 166 3 5 6 7 8 108 0\n168 -16 26 0 164 153 20 33 45 93 150 0\n169 29 26 0 164 165 153 142 168 167 97 166 157 1 9 11 14 17 109 0\n170 -29 0 145 10 37 47 61 70 112 0\n171 26 0 170 169 0\n172 -35 0 171 24 0\n173 -40 0 171 35 0\n174 -50 0 171 58 0\n175 -47 0 172 159 0\n176 39 0 173 140 175 158 107 0\n177 -49 0 176 54 0\n178 56 0 177 147 174 110 0\n179 -43 0 178 75 0\n180 -53 0 178 76 0\n181 0 179 180 149 172 114 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record040
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "cb0da3592e8789e1783e745c9ca5a9664d971725595553570d6354d8751d2745d0f5c3a2d8b32d2b2ae1b16c3b91d4731d2719e1725c3743c8f13e2c4b0d28a89a898568382e079c1345898a52926545895251560d4342d074c388c9314e0b22c2b06e0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 57), (facetIndex 64), (facetIndex 68), (facetIndex 73), (facetIndex 83)]))
 (.leaf ([(facetIndex 45), (facetIndex 56), (facetIndex 65), (facetIndex 69), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 76), (facetIndex 79), (facetIndex 80)]))
 (.branch 4
 (.leaf ([(facetIndex 37), (facetIndex 40), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 38), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 55)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 60), (facetIndex 62), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 63), (facetIndex 71), (facetIndex 72), (facetIndex 74)])))
 (.branch 8
 (.leaf ([(facetIndex 41), (facetIndex 49), (facetIndex 77), (facetIndex 78), (facetIndex 81), (facetIndex 82)]))
 (.branch 9
 (.leaf ([(facetIndex 58), (facetIndex 59), (facetIndex 61)]))
 (.leaf ([(facetIndex 53), (facetIndex 70)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7722772160669105510658588014494447433133373243z25;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0002 : List Nat := [5]
def grouped2_0003 : List Nat := [5, 6]
def grouped2_0004 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0005 : List Nat := [6]
def grouped2_0006 : List Nat := [7, 8, 9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record040" "{\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record040" 17

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record040" "{\"ridges\":[[20,324],[26,321],[46,324],[56,321],[62,324],[63,385],[66,324],[67,324],[69,324],[71,385],[72,385],[74,321],[75,321]],\"owners\":[[26,321,[20,46,62,66,67],[56,74,75]],[56,321,[20,62,66,67],[26,46,74,75]],[74,321,[20,46,66,67],[26,56,62,75]],[75,321,[20,46,62,67],[26,56,66,74]],[20,324,[],[46,62,66,67,69]],[46,324,[],[20,62,66,67,69]],[62,324,[],[20,46,66,67,69]],[66,324,[],[20,46,62,67,69]],[67,324,[],[20,46,62,66,69]],[69,324,[],[20,46,62,66,67]],[63,385,[26,56,75],[24,54,69,71,72]],[71,385,[26,56,69],[24,54,63,72,75]],[72,385,[26,56,69,75],[24,54,63,71]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record040" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record040\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-2,1,3,5,7,8],[-4,1,5,7,8],[-12,1,3,7,8],[-13,1,3,5,8],[-1],[-3],[-5],[-7],[-8],[-9],[-6,2,4,13],[-10,2,4,9],[-11,2,4,9,13],[-14,6,10,11,12],[-15,14],[-16,15],[-17,16],[17]],\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":26,\"owners\":[20,46,62,66,67]},{\"tag\":\"mate\",\"ridge\":321,\"a\":56,\"owners\":[20,62,66,67]},{\"tag\":\"mate\",\"ridge\":321,\"a\":74,\"owners\":[20,46,66,67]},{\"tag\":\"mate\",\"ridge\":321,\"a\":75,\"owners\":[20,46,62,67]},{\"tag\":\"mate\",\"ridge\":324,\"a\":20,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":324,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":324,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":324,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":324,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":324,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":385,\"a\":63,\"owners\":[26,56,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":71,\"owners\":[26,56,69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":72,\"owners\":[26,56,69,75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[63,71,72,74],\"full_literals\":[-14,6,10,11,12]},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-15,false,14],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-16,15,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-17,false,16],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "p cnf 17 18\n-2 1 3 5 7 8 0\n-4 1 5 7 8 0\n-12 1 3 7 8 0\n-13 1 3 5 8 0\n-1 0\n-3 0\n-5 0\n-7 0\n-8 0\n-9 0\n-6 2 4 13 0\n-10 2 4 9 0\n-11 2 4 9 13 0\n-14 6 10 11 12 0\n-15 14 0\n-16 15 0\n-17 16 0\n17 0\n"
  "19 -13 0 9 5 6 7 4 0\n20 -12 0 9 5 6 8 3 0\n21 -4 0 9 5 7 8 2 0\n22 -2 0 9 5 6 7 8 1 0\n23 -6 0 22 21 19 11 0\n24 -10 0 22 21 10 12 0\n25 -11 0 22 21 10 19 13 0\n26 -14 0 23 24 25 20 14 0\n27 -15 0 26 15 0\n28 -16 0 27 16 0\n29 -17 0 28 17 0\n30 0 29 18 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record040

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record044
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1d2569c6a98e6558d62ba1e4785e0f9d1565c5a94e5554d52b61d4745d0f6a368ce364cd3c2d8b52d2b2ae1b16c3ba1d8791d4719e1745c970dd0f23c4f8b1c254a2a468c6898a615a0e0b81e705518a51931625294558342d0758350cc388ca344c5382d0b0ac1b81c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2492492492492492492492492492492492492249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 65), (facetIndex 69), (facetIndex 73)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 46), (facetIndex 54), (facetIndex 68), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 77), (facetIndex 81), (facetIndex 85)]))
 (.branch 4
 (.leaf ([(facetIndex 52), (facetIndex 55), (facetIndex 56), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 45), (facetIndex 53), (facetIndex 57), (facetIndex 66), (facetIndex 75), (facetIndex 78), (facetIndex 87)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 48), (facetIndex 60), (facetIndex 61), (facetIndex 70), (facetIndex 76), (facetIndex 82), (facetIndex 88)]))
 (.leaf ([(facetIndex 50), (facetIndex 51), (facetIndex 62), (facetIndex 63), (facetIndex 64)])))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 49)]))
 (.branch 9
 (.leaf ([(facetIndex 67), (facetIndex 71), (facetIndex 74), (facetIndex 79), (facetIndex 83), (facetIndex 86)]))
 (.leaf ([(facetIndex 72), (facetIndex 84)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5482985218425480985018406665533433143667571450111z28;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [5, 6]
def grouped2_0009 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8, 9]
def grouped2_0012 : List Nat := [8]
def grouped2_0013 : List Nat := [8, 9]
def grouped2_0014 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record044" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record044" 42

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record044" "{\"ridges\":[[5,517],[20,69],[21,37],[22,37],[30,524],[31,70],[33,548],[39,44],[39,548],[46,517],[49,69],[49,70],[49,517],[51,517],[65,21],[65,37],[69,44],[71,69],[72,37],[72,69],[77,22],[77,44],[80,524],[81,164],[83,70],[84,70]],\"owners\":[[65,21,[1,20,44,45,46,70,71],[17,43,67,68]],[77,22,[1,31,44,45,46,82,83],[28,43,79,80]],[5,517,[19,22,68,73],[46,49,51]],[46,517,[19,22,73],[5,49,51,68]],[49,517,[19,22,68,73],[5,46,51]],[51,517,[19,22,68],[5,46,49,73]],[30,524,[19,39,68],[80]],[80,524,[19,39],[30,68]],[81,164,[21,72,73],[32,69,84,85]],[33,548,[22,39,73],[85]],[39,548,[22,33,73,85],[]]],\"edges\":[[23,[5,19,22,30,33,39,46,49,51,68,73,80,85]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record044" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record044\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-11],[-16,-1],[-16,-11],[-16,-12],[-16,-13],[-16,-14],[-18,-3],[-19,-18],[-20,-6],[-20,-15],[-21,-16],[-23,-20],[-24,-6],[-24,-15],[-24,-23],[-25,-11],[-25,-18],[-27,-9],[-27,-20],[-28,-16],[-30,-27],[-31,-11],[-31,-15],[-31,-24],[-31,-30],[-18,1,4,12,13,14,21,22],[-25,1,8,12,13,14,28,29],[-5,-6,-18],[-6,-18,-23],[-4,-16,-23],[-16,-22,-23],[-8,-16,-30],[-16,-29,-30],[-2,3,6,19,24],[-14,3,6,24],[-16,3,6,19,24],[-17,3,6,19],[-10,-20,-25],[-7,3,10,19],[-26,3,10],[-27,5,23,24],[-9,6,10,24],[-10,6,9,24,31],[-32,11,18,20,24],[-33,25,27,31],[-34,15,16],[-35,23,30],[-36,32],[-37,33],[-38,36],[-38,37],[-39,35],[-40,34],[-40,39],[-41,40],[-42,38],[-42,41],[42],[2,3,6,7,9,10,14,16,17,19,24,26,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":1},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":65,\"b\":19},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":22},{\"tag\":\"incompatible\",\"a\":69,\"b\":47},{\"tag\":\"incompatible\",\"a\":70,\"b\":49},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":22},{\"tag\":\"incompatible\",\"a\":73,\"b\":47},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":43},{\"tag\":\"incompatible\",\"a\":77,\"b\":65},{\"tag\":\"incompatible\",\"a\":81,\"b\":33},{\"tag\":\"incompatible\",\"a\":81,\"b\":69},{\"tag\":\"incompatible\",\"a\":82,\"b\":49},{\"tag\":\"incompatible\",\"a\":84,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":43},{\"tag\":\"incompatible\",\"a\":85,\"b\":47},{\"tag\":\"incompatible\",\"a\":85,\"b\":73},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"mate\",\"ridge\":21,\"a\":65,\"owners\":[1,20,44,45,46,70,71]},{\"tag\":\"mate\",\"ridge\":22,\"a\":77,\"owners\":[1,31,44,45,46,82,83]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[21,22,65]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[22,65,72]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[20,49,72]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[49,71,72]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[31,49,84]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[49,83,84]},{\"tag\":\"mate\",\"ridge\":517,\"a\":5,\"owners\":[19,22,68,73]},{\"tag\":\"mate\",\"ridge\":517,\"a\":46,\"owners\":[19,22,73]},{\"tag\":\"mate\",\"ridge\":517,\"a\":49,\"owners\":[19,22,68,73]},{\"tag\":\"mate\",\"ridge\":517,\"a\":51,\"owners\":[19,22,68]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[39,69,77]},{\"tag\":\"mate\",\"ridge\":524,\"a\":30,\"owners\":[19,39,68]},{\"tag\":\"mate\",\"ridge\":524,\"a\":80,\"owners\":[19,39]},{\"tag\":\"mate\",\"ridge\":164,\"a\":81,\"owners\":[21,72,73]},{\"tag\":\"mate\",\"ridge\":548,\"a\":33,\"owners\":[22,39,73]},{\"tag\":\"mate\",\"ridge\":548,\"a\":39,\"owners\":[22,33,73,85]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[43,65,69,73],\"full_literals\":[-32,11,18,20,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[77,81,85],\"full_literals\":[-33,25,27,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,49],\"full_literals\":[-34,15,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[72,84],\"full_literals\":[-35,23,30]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-37,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-38,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-40,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-42,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[5,19,22,30,33,39,46,49,51,68,73,80,85]}]}"
  "p cnf 42 59\n-15 -11 0\n-16 -1 0\n-16 -11 0\n-16 -12 0\n-16 -13 0\n-16 -14 0\n-18 -3 0\n-19 -18 0\n-20 -6 0\n-20 -15 0\n-21 -16 0\n-23 -20 0\n-24 -6 0\n-24 -15 0\n-24 -23 0\n-25 -11 0\n-25 -18 0\n-27 -9 0\n-27 -20 0\n-28 -16 0\n-30 -27 0\n-31 -11 0\n-31 -15 0\n-31 -24 0\n-31 -30 0\n-18 1 4 12 13 14 21 22 0\n-25 1 8 12 13 14 28 29 0\n-5 -6 -18 0\n-6 -18 -23 0\n-4 -16 -23 0\n-16 -22 -23 0\n-8 -16 -30 0\n-16 -29 -30 0\n-2 3 6 19 24 0\n-14 3 6 24 0\n-16 3 6 19 24 0\n-17 3 6 19 0\n-10 -20 -25 0\n-7 3 10 19 0\n-26 3 10 0\n-27 5 23 24 0\n-9 6 10 24 0\n-10 6 9 24 31 0\n-32 11 18 20 24 0\n-33 25 27 31 0\n-34 15 16 0\n-35 23 30 0\n-36 32 0\n-37 33 0\n-38 36 0\n-38 37 0\n-39 35 0\n-40 34 0\n-40 39 0\n-41 40 0\n-42 38 0\n-42 41 0\n42 0\n2 3 6 7 9 10 14 16 17 19 24 26 31 0\n"
  "60 38 0 58 56 0\n61 41 0 58 57 0\n62 36 0 60 50 0\n63 37 0 60 51 0\n64 40 0 61 55 0\n65 32 0 62 48 0\n66 33 0 63 49 0\n67 34 0 64 53 0\n68 39 0 64 54 0\n69 35 0 68 52 0\n70 -9 24 6 31 0 66 65 18 42 45 16 17 38 44 0\n71 -31 0 67 69 65 22 23 24 25 46 47 2 4 5 6 11 12 30 31 44 26 0\n72 -18 -6 0 71 66 13 17 29 28 45 41 0\n73 -11 0 67 1 3 46 0\n74 -6 0 73 65 9 13 72 44 0\n75 -20 0 67 69 71 66 10 12 19 46 47 45 2 4 5 6 20 32 33 27 0\n76 24 0 75 73 65 71 74 70 44 43 7 8 34 35 40 36 37 39 59 0\n77 -15 0 76 14 0\n78 -23 0 76 15 0\n79 16 0 77 67 46 0\n80 30 0 78 69 47 0\n81 -1 0 79 2 0\n82 -12 0 79 4 0\n83 -13 0 79 5 0\n84 -14 0 79 6 0\n85 -28 0 79 20 0\n86 -27 0 80 21 0\n87 -8 0 80 79 32 0\n88 -29 0 80 79 33 0\n89 25 0 86 66 71 45 0\n90 0 87 89 81 82 83 84 85 88 27 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00021.record044
