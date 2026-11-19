module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00001Frames
public import GraphInputsRow19Part00001Leaves
public import GraphInputsRow19Part00001Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00001.record042
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1e8e315c1f38a2e87ae1876c3a8e6386e1783e785c96a5693a5592e479e1745554756354d1b51d1743de0ea32cc7362cab1ac9b16c3bc1e8761c6785c570dd0f23c4f0bc1f1e14c170aa0e81ee0471c15451568328c3381c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da4d26db6d26db6da49269b4d249a6da49b4936da249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.leaf ([(facetIndex 3)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.leaf ([(facetIndex 7)])))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)])))
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)]))))
 (.branch 14
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)])))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.leaf ([(facetIndex 15)]))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨4, 18364758544493064720⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 16
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 36), (facetIndex 37)]))
 (.branch 2
 (.leaf ([(facetIndex 27), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 16), (facetIndex 21), (facetIndex 22), (facetIndex 23)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 35), (facetIndex 65)]))
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 45), (facetIndex 68)])))
 (.branch 6
 (.leaf ([(facetIndex 34), (facetIndex 44), (facetIndex 48)]))
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 64), (facetIndex 67)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4c1e000036000005265100800743003200490002000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 55)]))
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 17), (facetIndex 18), (facetIndex 24)]))
 (.branch 4
 (.leaf ([(facetIndex 29), (facetIndex 38), (facetIndex 58)]))
 (.leaf ([(facetIndex 31), (facetIndex 41), (facetIndex 62)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 25), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 59), (facetIndex 66), (facetIndex 69)])))
 (.branch 8
 (.leaf ([(facetIndex 19), (facetIndex 20), (facetIndex 30), (facetIndex 40)]))
 (.branch 9
 (.leaf ([(facetIndex 33), (facetIndex 43), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 63)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "160060094556300011008800000804703000080473000520007722z11;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0, 1, 2, 3]
def grouped1_0001 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0003 : List Nat := [4]
def grouped1_0004 : List Nat := [4, 5]
def grouped1_0005 : List Nat := [4, 5, 6, 7]
def grouped1_0006 : List Nat := [5]
def grouped1_0007 : List Nat := [6]
def grouped1_0008 : List Nat := [6, 7]
def grouped1_0009 : List Nat := [7]
def grouped1_0010 : List Nat := [8]
def grouped1_0011 : List Nat := [8, 9]
def grouped1_0012 : List Nat := [8, 9, 10, 11]
def grouped1_0013 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]
def grouped1_0014 : List Nat := [9]
def grouped1_0015 : List Nat := [10, 11]
def grouped1_0016 : List Nat := [12]
def grouped1_0017 : List Nat := [12, 13]
def grouped1_0018 : List Nat := [12, 13, 14, 15]
def grouped1_0019 : List Nat := [13]
def grouped1_0020 : List Nat := [14]
def grouped1_0021 : List Nat := [14, 15]
def grouped1_0022 : List Nat := [15]
def grouped2_0023 : List Nat := [0]
def grouped2_0024 : List Nat := [0, 1, 2]
def grouped2_0026 : List Nat := [1]
def grouped2_0027 : List Nat := [1, 2]
def grouped2_0028 : List Nat := [2]
def grouped2_0029 : List Nat := [3]
def grouped2_0030 : List Nat := [3, 4]
def grouped2_0031 : List Nat := [3, 4, 5, 6]
def grouped2_0032 : List Nat := [4]
def grouped2_0033 : List Nat := [5]
def grouped2_0034 : List Nat := [5, 6]
def grouped2_0035 : List Nat := [6]
def grouped3_0036 : List Nat := [0]
def grouped3_0037 : List Nat := [0, 1]
def grouped3_0038 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0040 : List Nat := [1]
def grouped3_0041 : List Nat := [2]
def grouped3_0042 : List Nat := [2, 3, 4]
def grouped3_0043 : List Nat := [3]
def grouped3_0044 : List Nat := [3, 4]
def grouped3_0045 : List Nat := [4]
def grouped3_0046 : List Nat := [5]
def grouped3_0047 : List Nat := [5, 6]
def grouped3_0048 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0049 : List Nat := [6]
def grouped3_0050 : List Nat := [7]
def grouped3_0051 : List Nat := [7, 8, 9]
def grouped3_0052 : List Nat := [8]
def grouped3_0053 : List Nat := [8, 9]
def grouped3_0054 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_matrix_checked

def leafCount : Nat := 20
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 16), (facetIndex 26), (facetIndex 35), (facetIndex 44), (facetIndex 46), (facetIndex 55), (facetIndex 61), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 70)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 22), (facetIndex 26), (facetIndex 35), (facetIndex 46), (facetIndex 48), (facetIndex 55), (facetIndex 56), (facetIndex 61), (facetIndex 66), (facetIndex 68), (facetIndex 70)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 1), (facetIndex 12), (facetIndex 16), (facetIndex 35), (facetIndex 37), (facetIndex 44), (facetIndex 46), (facetIndex 55), (facetIndex 60), (facetIndex 64), (facetIndex 68), (facetIndex 69), (facetIndex 70)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 1), (facetIndex 12), (facetIndex 22), (facetIndex 35), (facetIndex 37), (facetIndex 46), (facetIndex 48), (facetIndex 55), (facetIndex 56), (facetIndex 60), (facetIndex 68), (facetIndex 69), (facetIndex 70)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 2), (facetIndex 10), (facetIndex 23), (facetIndex 32), (facetIndex 37), (facetIndex 44), (facetIndex 46), (facetIndex 55), (facetIndex 60), (facetIndex 64), (facetIndex 68), (facetIndex 69), (facetIndex 70)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 10), (facetIndex 12), (facetIndex 23), (facetIndex 35), (facetIndex 37), (facetIndex 44), (facetIndex 46), (facetIndex 51), (facetIndex 54), (facetIndex 60), (facetIndex 64), (facetIndex 68), (facetIndex 69)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 10), (facetIndex 12), (facetIndex 23), (facetIndex 35), (facetIndex 37), (facetIndex 44), (facetIndex 46), (facetIndex 52), (facetIndex 53), (facetIndex 60), (facetIndex 64), (facetIndex 68), (facetIndex 69)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 10), (facetIndex 12), (facetIndex 23), (facetIndex 35), (facetIndex 37), (facetIndex 44), (facetIndex 46), (facetIndex 55), (facetIndex 60), (facetIndex 64), (facetIndex 68), (facetIndex 69), (facetIndex 70)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 2), (facetIndex 15), (facetIndex 23), (facetIndex 36), (facetIndex 42), (facetIndex 44), (facetIndex 47), (facetIndex 55), (facetIndex 57), (facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 70)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 2), (facetIndex 14), (facetIndex 23), (facetIndex 36), (facetIndex 45), (facetIndex 47), (facetIndex 48), (facetIndex 55), (facetIndex 57), (facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 70)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 27), (facetIndex 34), (facetIndex 36), (facetIndex 45), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 67), (facetIndex 69), (facetIndex 70)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 9), (facetIndex 14), (facetIndex 21), (facetIndex 27), (facetIndex 36), (facetIndex 45), (facetIndex 48), (facetIndex 55), (facetIndex 57), (facetIndex 60), (facetIndex 65), (facetIndex 69), (facetIndex 70)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 1), (facetIndex 14), (facetIndex 16), (facetIndex 34), (facetIndex 36), (facetIndex 45), (facetIndex 47), (facetIndex 55), (facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 70)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 1), (facetIndex 14), (facetIndex 21), (facetIndex 36), (facetIndex 45), (facetIndex 47), (facetIndex 48), (facetIndex 55), (facetIndex 57), (facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 70)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 5), (facetIndex 10), (facetIndex 23), (facetIndex 34), (facetIndex 36), (facetIndex 42), (facetIndex 47), (facetIndex 55), (facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 70)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 23), (facetIndex 34), (facetIndex 36), (facetIndex 45), (facetIndex 47), (facetIndex 52), (facetIndex 53), (facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 67)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 23), (facetIndex 34), (facetIndex 36), (facetIndex 45), (facetIndex 47), (facetIndex 51), (facetIndex 54), (facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 67)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 23), (facetIndex 34), (facetIndex 36), (facetIndex 45), (facetIndex 47), (facetIndex 55), (facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 70)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 5), (facetIndex 15), (facetIndex 23), (facetIndex 32), (facetIndex 34), (facetIndex 37), (facetIndex 46), (facetIndex 55), (facetIndex 56), (facetIndex 60), (facetIndex 68), (facetIndex 69), (facetIndex 70)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 5), (facetIndex 12), (facetIndex 23), (facetIndex 35), (facetIndex 37), (facetIndex 46), (facetIndex 48), (facetIndex 55), (facetIndex 56), (facetIndex 60), (facetIndex 68), (facetIndex 69), (facetIndex 70)]
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

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00001.record042" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0008\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0027\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0024\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0030\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0034\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0031\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0037\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0037\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0044\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0042\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0038\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0038\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0038\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0047\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0047\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0053\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0053\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0051\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0051\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0051\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0048\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0048\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0048\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00001.record042" 133

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00001.record042" "{\"ridges\":[[8,97],[12,168],[15,104],[16,7],[17,35],[17,45],[20,267],[22,7],[23,19],[23,22],[26,517],[26,518],[26,641],[26,642],[27,518],[27,769],[27,772],[30,153],[31,75],[32,161],[32,168],[34,35],[34,81],[34,97],[35,162],[36,35],[36,161],[36,162],[36,515],[37,642],[37,769],[37,896],[39,81],[40,281],[41,45],[42,321],[42,328],[43,141],[44,49],[44,97],[44,112],[45,324],[47,772],[47,896],[48,81],[48,97],[48,104],[49,153],[50,281],[53,297],[55,480],[56,28],[56,42],[56,56],[63,390],[64,26],[64,104],[65,168],[66,392],[67,28],[67,104],[68,324],[69,268],[70,480]],\"owners\":[[16,7,[1,24,25,26,27],[0,17,18,19,20,21,22]],[22,7,[1,17,19,20,25,26,27],[0,16,18,21,24]],[23,19,[2,28,29,30,34,35],[0,16,22]],[23,22,[10,56,57,62],[0,21,22]],[36,515,[1,23,27],[4,37]],[26,517,[7,46],[1,23,47]],[26,518,[61],[1,23,27,60,63]],[27,518,[60],[1,23,26,61,63]],[44,49,[2,28,35,49],[8,21,38,48]],[32,161,[55],[3,35,36,49,51,53]],[36,161,[49,51,53,55],[3,32,35]],[35,162,[12],[3,36,65]],[36,162,[12,65],[3,35]],[26,641,[9],[4,36,47]],[26,642,[66],[4,36,37,60,63]],[37,642,[60],[4,26,36,63,66]],[34,81,[5,39,45,50],[8,22,29,48]],[39,81,[8,34],[5,22,29,45,48,50]],[48,81,[5,22,45],[8,29,34,39,50]],[42,321,[55],[6,45,46,50,52,54]],[45,324,[14],[6,46,68]],[68,324,[6,46],[14,45]],[27,769,[9],[7,37,46]],[37,769,[7,46],[9,27]],[27,772,[69],[7,46,47,61,63]],[47,772,[61],[7,27,46,63,69]],[8,97,[24,31,41,51,52,55],[34,44,48]],[34,97,[41,51,52,55],[8,24,31,44,48]],[44,97,[31,51,52,55],[8,24,34,41,48]],[48,97,[24,55],[8,31,34,41,44,51,52]],[44,112,[15,64],[8,34,62,67]],[37,896,[69],[9,47,63,66]],[47,896,[66],[9,37,63,69]],[64,26,[10,16,30],[11,28,29,57,65]],[56,28,[13,39,40,68],[10,16,38,67]],[67,28,[10,16,40],[13,38,39,56,68]],[56,42,[12,31,32],[11,17,28,58,64]],[56,56,[15,48,49],[11,28,38,65,67]],[12,168,[49,51,53,70],[32,65]],[32,168,[70],[12,49,51,53,65]],[65,168,[51,53,70],[12,32,49]],[69,268,[14,20,40,42,68],[43,59,61]],[42,328,[70],[14,50,52,54,68]],[15,104,[31,41,51,52,58,70],[48,64,67]],[48,104,[58,70],[15,31,41,51,52,64,67]],[64,104,[41,51,52,70],[15,31,48,58,67]],[67,104,[31,51,52,70],[15,41,48,58,64]],[17,45,[38,41],[]],[41,45,[17,38],[]],[31,75,[18,29],[]],[43,141,[19],[]],[20,267,[33],[]],[63,390,[25,59],[]],[30,153,[49],[]],[49,153,[30],[]],[66,392,[43,53,54,70],[33,59,69]],[40,281,[50],[]],[50,281,[40],[]],[53,297,[52],[]],[55,480,[70],[]],[70,480,[55],[]]],\"edges\":[[35,[8,15,24,31,34,41,44,48,51,52,55,58,62,64,67,70]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00001.record042" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00001.record042\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-16],[-23,-20],[-24,-20],[-24,-23],[-29,-13],[-31,-18],[-31,-19],[-31,-25],[-32,-31],[-33,-16],[-33,-22],[-33,-29],[-33,-30],[-33,-32],[-34,-24],[-34,-30],[-35,-31],[-36,-25],[-36,-29],[-39,-13],[-39,-25],[-39,-29],[-41,-18],[-41,-19],[-41,-36],[-42,-19],[-42,-21],[-42,-41],[-43,-22],[-43,-24],[-43,-39],[-43,-42],[-44,-23],[-44,-34],[-45,-13],[-45,-25],[-45,-29],[-45,-36],[-45,-39],[-46,-25],[-46,-29],[-46,-32],[-47,-36],[-47,-39],[-47,-42],[-48,-13],[-49,-13],[-50,-13],[-53,-13],[-53,-14],[-53,-18],[-53,-21],[-53,-25],[-53,-26],[-53,-41],[-54,-31],[-54,-36],[-55,-53],[-57,-16],[-58,-30],[-59,-31],[-60,-23],[-60,-30],[-60,-34],[-60,-40],[-60,-57],[-60,-58],[-61,-19],[-61,-21],[-61,-25],[-61,-26],[-61,-28],[-61,-31],[-61,-35],[-61,-45],[-61,-59],[-62,-46],[-62,-53],[-62,-61],[-64,-36],[-64,-41],[-64,-45],[-65,-15],[-65,-38],[-65,-42],[-65,-47],[-65,-54],[-65,-55],[-65,-64],[-13,1,21,22,23,24],[-19,1,14,16,17,22,23,24],[-20,2,25,26,27,31,32],[-20,8,53,54,59],[-33,1,20,24],[-23,5,43],[-23,58],[-24,57],[-14,-31,-33],[-41,2,25,32,46],[-29,52],[-33,46,48,50,52],[-32,9],[-33,9,62],[-23,7],[-23,63],[-34,57],[-31,3,36,42,47],[-36,6,31],[-45,3,19,42],[-39,52],[-42,11],[-65,4,43],[-24,7],[-34,5,43],[-24,66],[-44,58],[-6,21,28,38,48,49,52],[-31,38,48,49,52],[-41,28,48,49,52],[-45,21,52],[-41,12,61],[-34,66],[-44,63],[-61,8,13,27],[-53,10,36,37,65],[-64,8,13,37],[-53,9,28,29],[-53,12,45,46],[-9,46,48,50,67],[-29,67],[-62,48,50,67],[-66,11,17,37,39,65],[-39,67],[-12,28,38,48,49,55,67],[-45,55,67],[-61,38,48,49,67],[-64,28,48,49,67],[-14,35,38],[-38,14,35],[-28,15,26],[-40,16],[-17,30],[-60,22,56],[-27,46],[-46,27],[-63,40,50,51,67],[-37,47],[-47,37],[-50,49],[-52,67],[-67,52],[-3,68],[-4,69],[-5,70],[-6,71],[-7,72],[-9,73],[-10,74],[-11,75],[-68,76],[-69,-70,77],[-77,78],[-76,-77,79],[-78,80],[-79,81],[-71,-72,82],[-82,83],[-73,84],[-73,-74,85],[-75,86],[-84,87],[-85,-86,88],[-87,89],[-88,90],[-83,-87,90],[-90,91],[-80,-89,91],[-81,91],[-91],[-92,23,33,34],[-93,24,43,44],[-94,13,18,19,20],[-95,25,29,32,62],[-96,36,39,42,65],[-97,31,41,45],[-98,53,54,61,64],[-99,93],[-99,94],[-100,92],[-100,99],[-101,95],[-101,96],[-102,97],[-102,98],[-103,101],[-103,102],[-104,100],[-104,103],[104],[-105,48,49,52],[-48,105],[-49,105],[-52,105],[-106,50,51,67],[-67,106],[-107,14,15,21],[-21,107],[-108,26,35,55],[-26,108],[-55,108],[-109,28,38,59],[-28,109],[-38,109],[-59,109],[-110,22,57,58],[-22,110],[-58,110],[-56,111],[-63,111],[-112,16,17,27,37],[-27,112],[-37,112],[-113,30,40,46,47],[-114,60],[-106,115],[-116,105],[-105,115],[-116,106],[-105,-106,116],[-117,108,109],[-109,117],[-108,117],[-118,107,117],[-117,118],[-107,118],[-118,119],[-115,119],[-120,116,118],[-116,-118,121],[-111,122],[-123,110],[-110,122],[-110,-111,123],[-124,113,114],[-125,113],[-125,114],[-126,112,124],[-127,112,125],[-128,125],[-112,-125,128],[-130,123,127],[-122,-128,131],[-123,129],[-130,126],[-132,120,130],[-119,-131,133],[-121,-129,133],[132],[-133],[-7,-9,-13,-23,-32,-41,-43,-52,-58,-61,-63,-65,-67],[-7,-9,-19,-23,-32,-43,-45,-52,-53,-58,-63,-65,-67],[-1,-9,-13,-32,-34,-41,-43,-52,-57,-61,-65,-66,-67],[-1,-9,-19,-32,-34,-43,-45,-52,-53,-57,-65,-66,-67],[-2,-8,-20,-29,-34,-41,-43,-52,-57,-61,-65,-66,-67],[-8,-9,-20,-32,-34,-41,-43,-48,-51,-57,-61,-65,-66],[-8,-9,-20,-32,-34,-41,-43,-49,-50,-57,-61,-65,-66],[-8,-9,-20,-32,-34,-41,-43,-52,-57,-61,-65,-66,-67],[-2,-12,-20,-33,-39,-41,-44,-52,-54,-58,-62,-63,-67],[-2,-11,-20,-33,-42,-44,-45,-52,-54,-58,-62,-63,-67],[-7,-11,-13,-24,-31,-33,-42,-52,-57,-62,-64,-66,-67],[-7,-11,-18,-24,-33,-42,-45,-52,-54,-57,-62,-66,-67],[-1,-11,-13,-31,-33,-42,-44,-52,-58,-62,-63,-64,-67],[-1,-11,-18,-33,-42,-44,-45,-52,-54,-58,-62,-63,-67],[-3,-8,-20,-31,-33,-39,-44,-52,-58,-62,-63,-64,-67],[-8,-11,-20,-31,-33,-42,-44,-49,-50,-58,-62,-63,-64],[-8,-11,-20,-31,-33,-42,-44,-48,-51,-58,-62,-63,-64],[-8,-11,-20,-31,-33,-42,-44,-52,-58,-62,-63,-64,-67],[-3,-12,-20,-29,-31,-34,-43,-52,-53,-57,-65,-66,-67],[-3,-9,-20,-32,-34,-43,-45,-52,-53,-57,-65,-66,-67],[6,12,21,28,31,38,41,45,48,49,52,55,59,61,64,67]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":26,\"b\":19},{\"tag\":\"incompatible\",\"a\":26,\"b\":23},{\"tag\":\"incompatible\",\"a\":27,\"b\":23},{\"tag\":\"incompatible\",\"a\":27,\"b\":26},{\"tag\":\"incompatible\",\"a\":32,\"b\":16},{\"tag\":\"incompatible\",\"a\":34,\"b\":21},{\"tag\":\"incompatible\",\"a\":34,\"b\":22},{\"tag\":\"incompatible\",\"a\":34,\"b\":28},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":19},{\"tag\":\"incompatible\",\"a\":36,\"b\":25},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":36,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":27},{\"tag\":\"incompatible\",\"a\":37,\"b\":33},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":28},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":42,\"b\":16},{\"tag\":\"incompatible\",\"a\":42,\"b\":28},{\"tag\":\"incompatible\",\"a\":42,\"b\":32},{\"tag\":\"incompatible\",\"a\":44,\"b\":21},{\"tag\":\"incompatible\",\"a\":44,\"b\":22},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":22},{\"tag\":\"incompatible\",\"a\":45,\"b\":24},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":25},{\"tag\":\"incompatible\",\"a\":46,\"b\":27},{\"tag\":\"incompatible\",\"a\":46,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":26},{\"tag\":\"incompatible\",\"a\":47,\"b\":37},{\"tag\":\"incompatible\",\"a\":48,\"b\":16},{\"tag\":\"incompatible\",\"a\":48,\"b\":28},{\"tag\":\"incompatible\",\"a\":48,\"b\":32},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":48,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":28},{\"tag\":\"incompatible\",\"a\":49,\"b\":32},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":16},{\"tag\":\"incompatible\",\"a\":52,\"b\":16},{\"tag\":\"incompatible\",\"a\":53,\"b\":16},{\"tag\":\"incompatible\",\"a\":56,\"b\":16},{\"tag\":\"incompatible\",\"a\":56,\"b\":17},{\"tag\":\"incompatible\",\"a\":56,\"b\":21},{\"tag\":\"incompatible\",\"a\":56,\"b\":24},{\"tag\":\"incompatible\",\"a\":56,\"b\":28},{\"tag\":\"incompatible\",\"a\":56,\"b\":29},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":34},{\"tag\":\"incompatible\",\"a\":57,\"b\":39},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":19},{\"tag\":\"incompatible\",\"a\":61,\"b\":33},{\"tag\":\"incompatible\",\"a\":62,\"b\":34},{\"tag\":\"incompatible\",\"a\":63,\"b\":26},{\"tag\":\"incompatible\",\"a\":63,\"b\":33},{\"tag\":\"incompatible\",\"a\":63,\"b\":37},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":22},{\"tag\":\"incompatible\",\"a\":64,\"b\":24},{\"tag\":\"incompatible\",\"a\":64,\"b\":28},{\"tag\":\"incompatible\",\"a\":64,\"b\":29},{\"tag\":\"incompatible\",\"a\":64,\"b\":31},{\"tag\":\"incompatible\",\"a\":64,\"b\":34},{\"tag\":\"incompatible\",\"a\":64,\"b\":38},{\"tag\":\"incompatible\",\"a\":64,\"b\":48},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":49},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":39},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":67,\"b\":48},{\"tag\":\"incompatible\",\"a\":68,\"b\":18},{\"tag\":\"incompatible\",\"a\":68,\"b\":41},{\"tag\":\"incompatible\",\"a\":68,\"b\":45},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":57},{\"tag\":\"incompatible\",\"a\":68,\"b\":58},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"mate\",\"ridge\":7,\"a\":16,\"owners\":[1,24,25,26,27]},{\"tag\":\"mate\",\"ridge\":7,\"a\":22,\"owners\":[1,17,19,20,25,26,27]},{\"tag\":\"mate\",\"ridge\":19,\"a\":23,\"owners\":[2,28,29,30,34,35]},{\"tag\":\"mate\",\"ridge\":22,\"a\":23,\"owners\":[10,56,57,62]},{\"tag\":\"mate\",\"ridge\":515,\"a\":36,\"owners\":[1,23,27]},{\"tag\":\"mate\",\"ridge\":517,\"a\":26,\"owners\":[7,46]},{\"tag\":\"mate\",\"ridge\":518,\"a\":26,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":518,\"a\":27,\"owners\":[60]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[17,34,36]},{\"tag\":\"mate\",\"ridge\":49,\"a\":44,\"owners\":[2,28,35,49]},{\"tag\":\"mate\",\"ridge\":161,\"a\":32,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":161,\"a\":36,\"owners\":[49,51,53,55]},{\"tag\":\"mate\",\"ridge\":162,\"a\":35,\"owners\":[12]},{\"tag\":\"mate\",\"ridge\":162,\"a\":36,\"owners\":[12,65]},{\"tag\":\"mate\",\"ridge\":641,\"a\":26,\"owners\":[9]},{\"tag\":\"mate\",\"ridge\":642,\"a\":26,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":642,\"a\":37,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":81,\"a\":34,\"owners\":[5,39,45,50]},{\"tag\":\"mate\",\"ridge\":81,\"a\":39,\"owners\":[8,34]},{\"tag\":\"mate\",\"ridge\":81,\"a\":48,\"owners\":[5,22,45]},{\"tag\":\"mate\",\"ridge\":321,\"a\":42,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":324,\"a\":45,\"owners\":[14]},{\"tag\":\"mate\",\"ridge\":324,\"a\":68,\"owners\":[6,46]},{\"tag\":\"mate\",\"ridge\":769,\"a\":27,\"owners\":[9]},{\"tag\":\"mate\",\"ridge\":769,\"a\":37,\"owners\":[7,46]},{\"tag\":\"mate\",\"ridge\":772,\"a\":27,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":772,\"a\":47,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":97,\"a\":8,\"owners\":[24,31,41,51,52,55]},{\"tag\":\"mate\",\"ridge\":97,\"a\":34,\"owners\":[41,51,52,55]},{\"tag\":\"mate\",\"ridge\":97,\"a\":44,\"owners\":[31,51,52,55]},{\"tag\":\"mate\",\"ridge\":97,\"a\":48,\"owners\":[24,55]},{\"tag\":\"mate\",\"ridge\":112,\"a\":44,\"owners\":[15,64]},{\"tag\":\"mate\",\"ridge\":896,\"a\":37,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":896,\"a\":47,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":26,\"a\":64,\"owners\":[10,16,30]},{\"tag\":\"mate\",\"ridge\":28,\"a\":56,\"owners\":[13,39,40,68]},{\"tag\":\"mate\",\"ridge\":28,\"a\":67,\"owners\":[10,16,40]},{\"tag\":\"mate\",\"ridge\":42,\"a\":56,\"owners\":[12,31,32]},{\"tag\":\"mate\",\"ridge\":56,\"a\":56,\"owners\":[15,48,49]},{\"tag\":\"mate\",\"ridge\":168,\"a\":12,\"owners\":[49,51,53,70]},{\"tag\":\"mate\",\"ridge\":168,\"a\":32,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":168,\"a\":65,\"owners\":[51,53,70]},{\"tag\":\"mate\",\"ridge\":268,\"a\":69,\"owners\":[14,20,40,42,68]},{\"tag\":\"mate\",\"ridge\":328,\"a\":42,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":104,\"a\":15,\"owners\":[31,41,51,52,58,70]},{\"tag\":\"mate\",\"ridge\":104,\"a\":48,\"owners\":[58,70]},{\"tag\":\"mate\",\"ridge\":104,\"a\":64,\"owners\":[41,51,52,70]},{\"tag\":\"mate\",\"ridge\":104,\"a\":67,\"owners\":[31,51,52,70]},{\"tag\":\"mate\",\"ridge\":45,\"a\":17,\"owners\":[38,41]},{\"tag\":\"mate\",\"ridge\":45,\"a\":41,\"owners\":[17,38]},{\"tag\":\"mate\",\"ridge\":75,\"a\":31,\"owners\":[18,29]},{\"tag\":\"mate\",\"ridge\":141,\"a\":43,\"owners\":[19]},{\"tag\":\"mate\",\"ridge\":267,\"a\":20,\"owners\":[33]},{\"tag\":\"mate\",\"ridge\":390,\"a\":63,\"owners\":[25,59]},{\"tag\":\"mate\",\"ridge\":153,\"a\":30,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":153,\"a\":49,\"owners\":[30]},{\"tag\":\"mate\",\"ridge\":392,\"a\":66,\"owners\":[43,53,54,70]},{\"tag\":\"mate\",\"ridge\":281,\"a\":40,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":281,\"a\":50,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":297,\"a\":53,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":480,\"a\":55,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":480,\"a\":70,\"owners\":[55]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-3,68]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-4,69]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-5,70]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-6,71]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-7,72]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-9,73]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-10,74]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-11,75]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,76],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-70,77],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0005\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-77,78],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0005\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-76,-77,79],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-78,80],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-79,81],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-72,82],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,83],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,84],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-74,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0018\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-85,-86,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-88,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0013\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-83,-87,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-90,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-89,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,91],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":2,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[26,36,37],\"full_literals\":[-92,23,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[27,46,47],\"full_literals\":[-93,24,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[16,21,22,23],\"full_literals\":[-94,13,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[28,32,35,65],\"full_literals\":[-95,25,29,32,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[39,42,45,68],\"full_literals\":[-96,36,39,42,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[34,44,48],\"full_literals\":[-97,31,41,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[56,57,64,67],\"full_literals\":[-98,53,54,61,64]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0028\",\"joined_name\":\"grouped2_0027\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-99,93,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0028\",\"joined_name\":\"grouped2_0027\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-99,false,94],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0023\",\"right_name\":\"grouped2_0027\",\"joined_name\":\"grouped2_0024\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-100,92,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0023\",\"right_name\":\"grouped2_0027\",\"joined_name\":\"grouped2_0024\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-100,false,99],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0032\",\"joined_name\":\"grouped2_0030\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-101,95,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0032\",\"joined_name\":\"grouped2_0030\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-101,false,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"grouped2_0034\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-102,97,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"grouped2_0034\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-102,false,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0030\",\"right_name\":\"grouped2_0034\",\"joined_name\":\"grouped2_0031\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-103,101,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0030\",\"right_name\":\"grouped2_0034\",\"joined_name\":\"grouped2_0031\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-103,false,102],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0024\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-104,100,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0024\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-104,false,103],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[51,52,55],\"full_literals\":[-105,48,49,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":51,\"full_literals\":[-48,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-49,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-52,105]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[53,54,70],\"full_literals\":[-106,50,51,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-67,106]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[17,18,24],\"full_literals\":[-107,14,15,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":24,\"full_literals\":[-21,107]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[29,38,58],\"full_literals\":[-108,26,35,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":29,\"full_literals\":[-26,108]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":58,\"full_literals\":[-55,108]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[31,41,62],\"full_literals\":[-109,28,38,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":31,\"full_literals\":[-28,109]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":41,\"full_literals\":[-38,109]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":62,\"full_literals\":[-59,109]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[25,60,61],\"full_literals\":[-110,22,57,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":25,\"full_literals\":[-22,110]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":61,\"full_literals\":[-58,110]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":59,\"full_literals\":[-56,111]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":66,\"full_literals\":[-63,111]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[19,20,30,40],\"full_literals\":[-112,16,17,27,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":30,\"full_literals\":[-27,112]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":40,\"full_literals\":[-37,112]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[33,43,49,50],\"full_literals\":[-113,30,40,46,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[63],\"full_literals\":[-114,60]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0040\",\"joined_name\":\"grouped3_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,115],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0040\",\"joined_name\":\"grouped3_0037\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-116,105,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0040\",\"joined_name\":\"grouped3_0037\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,115],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0040\",\"joined_name\":\"grouped3_0037\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-116,false,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0040\",\"joined_name\":\"grouped3_0037\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-105,-106,116],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0043\",\"right_name\":\"grouped3_0045\",\"joined_name\":\"grouped3_0044\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-117,108,109],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0043\",\"right_name\":\"grouped3_0045\",\"joined_name\":\"grouped3_0044\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-109,117],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0043\",\"right_name\":\"grouped3_0045\",\"joined_name\":\"grouped3_0044\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-108,false,117],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0041\",\"right_name\":\"grouped3_0044\",\"joined_name\":\"grouped3_0042\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-118,107,117],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0041\",\"right_name\":\"grouped3_0044\",\"joined_name\":\"grouped3_0042\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-117,118],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0041\",\"right_name\":\"grouped3_0044\",\"joined_name\":\"grouped3_0042\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-107,false,118],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0037\",\"right_name\":\"grouped3_0042\",\"joined_name\":\"grouped3_0038\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-118,119],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0037\",\"right_name\":\"grouped3_0042\",\"joined_name\":\"grouped3_0038\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-115,false,119],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0037\",\"right_name\":\"grouped3_0042\",\"joined_name\":\"grouped3_0038\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-120,116,118],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0037\",\"right_name\":\"grouped3_0042\",\"joined_name\":\"grouped3_0038\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-116,-118,121],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0046\",\"right_name\":\"grouped3_0049\",\"joined_name\":\"grouped3_0047\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-111,122],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0046\",\"right_name\":\"grouped3_0049\",\"joined_name\":\"grouped3_0047\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-123,110,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0046\",\"right_name\":\"grouped3_0049\",\"joined_name\":\"grouped3_0047\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,122],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0046\",\"right_name\":\"grouped3_0049\",\"joined_name\":\"grouped3_0047\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-111,123],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0052\",\"right_name\":\"grouped3_0054\",\"joined_name\":\"grouped3_0053\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-124,113,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0052\",\"right_name\":\"grouped3_0054\",\"joined_name\":\"grouped3_0053\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-125,113,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0052\",\"right_name\":\"grouped3_0054\",\"joined_name\":\"grouped3_0053\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-125,false,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0050\",\"right_name\":\"grouped3_0053\",\"joined_name\":\"grouped3_0051\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-126,112,124],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0050\",\"right_name\":\"grouped3_0053\",\"joined_name\":\"grouped3_0051\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-127,112,125],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0050\",\"right_name\":\"grouped3_0053\",\"joined_name\":\"grouped3_0051\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-128,false,125],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0050\",\"right_name\":\"grouped3_0053\",\"joined_name\":\"grouped3_0051\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-112,-125,128],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0047\",\"right_name\":\"grouped3_0051\",\"joined_name\":\"grouped3_0048\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-130,123,127],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0047\",\"right_name\":\"grouped3_0051\",\"joined_name\":\"grouped3_0048\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-122,-128,131],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0047\",\"right_name\":\"grouped3_0051\",\"joined_name\":\"grouped3_0048\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-123,false,129],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0047\",\"right_name\":\"grouped3_0051\",\"joined_name\":\"grouped3_0048\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-130,false,126],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0038\",\"right_name\":\"grouped3_0048\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-132,120,130],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0038\",\"right_name\":\"grouped3_0048\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-119,-131,133],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0038\",\"right_name\":\"grouped3_0048\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-121,-129,133],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[9,12,16,26,35,44,46,55,61,64,66,68,70]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[9,12,22,26,35,46,48,55,56,61,66,68,70]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[1,12,16,35,37,44,46,55,60,64,68,69,70]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[1,12,22,35,37,46,48,55,56,60,68,69,70]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[2,10,23,32,37,44,46,55,60,64,68,69,70]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[10,12,23,35,37,44,46,51,54,60,64,68,69]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[10,12,23,35,37,44,46,52,53,60,64,68,69]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[10,12,23,35,37,44,46,55,60,64,68,69,70]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[2,15,23,36,42,44,47,55,57,61,65,66,70]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[2,14,23,36,45,47,48,55,57,61,65,66,70]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[9,14,16,27,34,36,45,55,60,65,67,69,70]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[9,14,21,27,36,45,48,55,57,60,65,69,70]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[1,14,16,34,36,45,47,55,61,65,66,67,70]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[1,14,21,36,45,47,48,55,57,61,65,66,70]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[5,10,23,34,36,42,47,55,61,65,66,67,70]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[10,14,23,34,36,45,47,52,53,61,65,66,67]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[10,14,23,34,36,45,47,51,54,61,65,66,67]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[10,14,23,34,36,45,47,55,61,65,66,67,70]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[5,15,23,32,34,37,46,55,56,60,68,69,70]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[5,12,23,35,37,46,48,55,56,60,68,69,70]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[8,15,24,31,34,41,44,48,51,52,55,58,62,64,67,70]}]}"
  "281 -90 0 179 176 0\n282 -81 0 179 178 0\n283 -88 0 281 174 0\n284 -79 0 282 165 0\n285 100 0 199 197 0\n286 103 0 199 198 0\n287 92 0 285 189 0\n288 99 0 285 190 0\n289 101 0 286 195 0\n290 102 0 286 196 0\n291 93 0 288 187 0\n292 94 0 288 188 0\n293 95 0 289 191 0\n294 96 0 289 192 0\n295 97 0 290 193 0\n296 98 0 290 194 0\n297 119 0 236 237 234 235 225 227 231 232 207 205 201 202 203 212 213 214 210 135 119 137 134 118 136 117 280 0\n298 -131 0 297 259 256 0\n299 -128 0 298 249 252 246 240 242 224 218 216 143 0\n300 -125 0 299 245 246 250 224 221 222 63 65 145 148 223 0\n301 -16 0 287 1 10 59 180 106 0\n302 -40 0 301 141 0\n303 -30 0 287 13 16 60 180 96 0\n304 -17 0 303 142 0\n305 -46 0 293 40 41 42 77 183 0\n306 -27 0 305 144 0\n307 -47 0 294 43 44 45 86 184 0\n308 -37 0 307 147 0\n309 -113 0 307 303 302 305 223 0\n310 -112 0 308 304 301 306 220 0\n311 -127 0 310 300 248 0\n312 -130 0 310 311 309 287 254 247 251 244 241 224 62 64 66 67 180 215 11 0\n313 120 0 312 258 255 0\n314 -36 -53 0 293 295 78 55 53 19 38 183 185 9 0\n315 -42 -74 -53 0 292 291 283 287 78 51 49 26 32 111 182 159 2 3 170 181 172 34 169 180 157 103 0\n316 -39 -53 0 293 295 78 55 53 22 39 183 185 9 0\n317 65 -53 0 308 294 316 314 125 184 158 315 0\n318 43 77 33 -65 0 287 112 153 161 154 114 95 180 0\n319 19 -34 29 -53 0 295 179 293 292 122 106 317 53 78 183 14 54 83 140 127 157 168 171 173 177 164 162 318 58 55 9 185 135 52 120 85 51 49 182 109 279 0\n320 23 29 -53 0 295 179 293 287 304 301 317 53 78 183 14 54 83 140 127 157 168 171 173 177 164 162 318 30 29 58 55 9 185 135 52 120 50 180 106 122 319 91 263 0\n321 29 -53 0 293 295 179 292 54 317 83 140 78 58 55 53 52 51 49 183 127 9 14 157 185 168 120 135 171 173 177 164 162 318 320 2 96 104 105 182 261 0\n322 -53 0 305 295 307 292 287 284 49 51 55 314 317 85 321 12 37 100 130 128 185 7 107 182 152 2 160 180 163 106 122 278 318 0\n323 32 -65 0 295 296 322 293 305 306 292 287 291 87 89 186 73 75 185 23 79 70 68 183 99 5 12 100 130 124 182 2 3 180 34 106 122 264 181 0\n324 13 -67 -34 -65 0 295 296 322 179 306 292 151 122 106 323 14 102 157 168 171 173 177 164 162 318 87 89 186 73 75 185 23 68 124 182 267 0\n325 -67 23 -65 0 295 296 322 179 287 323 14 180 122 106 102 157 168 171 173 177 164 162 318 30 29 87 89 186 73 75 185 69 151 324 90 262 0\n326 -13 67 -9 0 305 46 48 129 0\n327 50 23 -65 0 313 179 287 306 292 295 296 322 305 87 89 186 73 75 185 23 68 323 102 325 326 182 124 14 180 122 106 157 168 171 173 177 164 162 318 83 69 84 74 138 206 71 88 208 76 72 211 230 233 238 228 204 129 265 0\n328 23 -65 0 295 296 322 179 287 306 292 323 14 102 157 168 171 173 177 164 162 318 87 89 186 73 75 185 23 68 180 106 122 325 326 124 182 327 149 266 0\n329 -65 0 322 296 295 313 179 292 83 84 87 88 89 186 68 69 71 72 73 74 75 76 211 138 208 185 230 206 23 233 238 226 323 14 102 157 168 171 173 177 164 162 318 328 2 96 104 105 182 46 47 326 200 260 0\n330 -23 -32 0 281 291 329 294 102 157 168 171 175 167 9 4 33 104 181 156 31 32 166 184 155 108 0\n331 -32 0 287 291 329 294 295 9 14 330 180 15 34 181 31 32 184 25 38 185 0\n332 -36 0 331 293 322 296 18 19 57 80 183 186 79 0\n333 -43 0 329 332 294 31 32 184 0\n334 42 -31 -33 -44 0 293 331 296 322 329 294 307 332 308 292 56 73 186 12 8 183 7 6 123 116 184 107 20 110 133 126 182 274 0\n335 -20 -67 -31 -33 -44 0 293 331 296 322 151 334 111 56 73 186 12 8 183 61 123 116 93 277 0\n336 -67 -31 -33 24 0 293 331 296 322 291 333 292 181 334 111 56 73 186 12 8 183 7 6 123 116 151 335 94 182 272 0\n337 -13 67 -62 0 46 48 131 0\n338 50 67 -31 -33 -44 0 296 322 308 293 331 292 302 305 7 6 12 8 183 337 182 56 73 186 126 150 334 111 123 116 146 101 276 0\n339 -31 -33 24 0 291 333 331 293 322 296 308 292 12 181 123 116 6 7 8 56 73 183 186 334 111 336 337 126 182 338 149 275 0\n340 67 31 0 329 332 294 295 133 150 184 27 28 120 185 0\n341 -20 -42 31 -33 -44 0 259 293 296 295 322 306 331 28 185 75 82 186 12 36 183 111 116 217 123 219 243 253 257 340 205 151 203 229 239 234 232 209 92 269 0\n342 -42 -33 24 0 291 333 295 331 293 322 296 292 339 340 151 12 181 123 116 26 28 111 185 35 36 75 82 183 186 341 94 182 273 0\n343 24 23 0 333 291 287 329 332 294 293 295 331 305 292 322 296 181 34 116 123 180 12 339 340 151 342 184 20 21 39 183 185 79 23 24 81 121 99 182 186 268 0\n344 -39 31 20 0 295 292 20 39 185 23 24 182 0\n345 31 23 0 287 308 304 329 332 294 295 292 331 293 322 296 343 15 180 12 115 113 97 3 340 151 344 132 184 26 28 185 35 36 75 82 182 183 186 271 0\n346 23 0 287 292 331 293 322 296 308 304 329 332 294 343 3 15 97 113 115 180 12 345 6 7 8 17 56 73 98 182 183 139 186 20 46 47 337 132 184 118 270 0\n347 -24 0 346 4 0\n348 -44 0 346 33 0\n349 0 348 347 291 333 181 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.l) :=
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
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.g)) :=
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
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00001.record042
