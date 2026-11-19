module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00033Frames
public import GraphInputsRow24Part00033Leaves
public import GraphInputsRow24Part00033Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce0f8cd0f4cb31c8f13c3c9aa3a8da2e87a598e6358b61db0e4b83e3c5a93a719a64d94e4b91e56539715954d54d4b51d70d4b61d4743d68d6338cd32cc73c2d8b32d2b2ac6b26c5b0ef0751cc749ca719c9715c3783d0f0bc1f3c0b81d0e24a8aa498663470986499c1615154c342c8b41c47"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "69a6db4934d26d34d369269b6926d269b6d26d24934da4934d369b249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.leaf ([(facetIndex 4)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 5)]))
 (.leaf ([(facetIndex 6)])))
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)]))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)])))
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.branch 14
 (.leaf ([(facetIndex 13)]))
 (.leaf ([(facetIndex 14)])))))
 (.branch 17
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)])))
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "9ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 20
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 65), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 22), (facetIndex 32), (facetIndex 41), (facetIndex 52)]))
 (.branch 4
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 31), (facetIndex 77)]))
 (.leaf ([(facetIndex 38), (facetIndex 71), (facetIndex 82)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 30), (facetIndex 56), (facetIndex 76), (facetIndex 88)]))
 (.leaf ([(facetIndex 35), (facetIndex 37), (facetIndex 39), (facetIndex 40)])))
 (.branch 8
 (.leaf ([(facetIndex 45), (facetIndex 53), (facetIndex 62), (facetIndex 69)]))
 (.branch 9
 (.leaf ([(facetIndex 25), (facetIndex 44), (facetIndex 73), (facetIndex 79), (facetIndex 83)]))
 (.leaf ([(facetIndex 64), (facetIndex 81), (facetIndex 90)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "905000084908035008040700119070000050072000000780026646060023530308002z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 85), (facetIndex 89)]))
 (.leaf ([(facetIndex 84), (facetIndex 87), (facetIndex 91)])))
 (.branch 3
 (.leaf ([(facetIndex 20), (facetIndex 21), (facetIndex 23), (facetIndex 86)]))
 (.branch 4
 (.leaf ([(facetIndex 48), (facetIndex 70), (facetIndex 72)]))
 (.leaf ([(facetIndex 24), (facetIndex 26), (facetIndex 34)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 33), (facetIndex 74), (facetIndex 78)]))
 (.leaf ([(facetIndex 42), (facetIndex 75), (facetIndex 80)])))
 (.branch 8
 (.leaf ([(facetIndex 28), (facetIndex 36), (facetIndex 43), (facetIndex 46), (facetIndex 47), (facetIndex 51), (facetIndex 55)]))
 (.branch 9
 (.leaf ([(facetIndex 54), (facetIndex 60), (facetIndex 61), (facetIndex 63), (facetIndex 68)]))
 (.leaf ([(facetIndex 59), (facetIndex 67)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100012010006050065030308900080889000780070037700760000070450000704042022z14;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def grouped1_0005 : List Nat := [1]
def grouped1_0006 : List Nat := [2]
def grouped1_0007 : List Nat := [2, 3, 4]
def grouped1_0008 : List Nat := [3]
def grouped1_0009 : List Nat := [3, 4]
def grouped1_0010 : List Nat := [4]
def grouped1_0011 : List Nat := [5]
def grouped1_0012 : List Nat := [5, 6]
def grouped1_0013 : List Nat := [5, 6, 7, 8, 9]
def grouped1_0014 : List Nat := [6]
def grouped1_0015 : List Nat := [7]
def grouped1_0016 : List Nat := [7, 8, 9]
def grouped1_0017 : List Nat := [8]
def grouped1_0018 : List Nat := [8, 9]
def grouped1_0019 : List Nat := [9]
def grouped1_0020 : List Nat := [10]
def grouped1_0021 : List Nat := [10, 11]
def grouped1_0022 : List Nat := [10, 11, 12, 13, 14]
def grouped1_0023 : List Nat := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def grouped1_0024 : List Nat := [11]
def grouped1_0025 : List Nat := [12]
def grouped1_0026 : List Nat := [12, 13, 14]
def grouped1_0027 : List Nat := [13]
def grouped1_0028 : List Nat := [13, 14]
def grouped1_0029 : List Nat := [14]
def grouped1_0030 : List Nat := [15]
def grouped1_0031 : List Nat := [15, 16]
def grouped1_0032 : List Nat := [15, 16, 17, 18, 19]
def grouped1_0033 : List Nat := [16]
def grouped1_0034 : List Nat := [17]
def grouped1_0035 : List Nat := [17, 18, 19]
def grouped1_0036 : List Nat := [18]
def grouped1_0037 : List Nat := [18, 19]
def grouped1_0038 : List Nat := [19]
def grouped2_0039 : List Nat := [0]
def grouped2_0040 : List Nat := [0, 1]
def grouped2_0041 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0043 : List Nat := [1]
def grouped2_0044 : List Nat := [2]
def grouped2_0045 : List Nat := [2, 3, 4]
def grouped2_0046 : List Nat := [3]
def grouped2_0047 : List Nat := [3, 4]
def grouped2_0048 : List Nat := [4]
def grouped2_0049 : List Nat := [5]
def grouped2_0050 : List Nat := [5, 6]
def grouped2_0051 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0052 : List Nat := [6]
def grouped2_0053 : List Nat := [7]
def grouped2_0054 : List Nat := [7, 8, 9]
def grouped2_0055 : List Nat := [8]
def grouped2_0056 : List Nat := [8, 9]
def grouped2_0057 : List Nat := [9]
def grouped3_0058 : List Nat := [0]
def grouped3_0059 : List Nat := [0, 1]
def grouped3_0060 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0062 : List Nat := [1]
def grouped3_0063 : List Nat := [2]
def grouped3_0064 : List Nat := [2, 3, 4]
def grouped3_0065 : List Nat := [3]
def grouped3_0066 : List Nat := [3, 4]
def grouped3_0067 : List Nat := [4]
def grouped3_0068 : List Nat := [5]
def grouped3_0069 : List Nat := [5, 6]
def grouped3_0070 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0071 : List Nat := [6]
def grouped3_0072 : List Nat := [7]
def grouped3_0073 : List Nat := [7, 8, 9]
def grouped3_0074 : List Nat := [8]
def grouped3_0075 : List Nat := [8, 9]
def grouped3_0076 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_matrix_checked

def leafCount : Nat := 316
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 77), (facetIndex 79), (facetIndex 84), (facetIndex 86), (facetIndex 88)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 77), (facetIndex 81), (facetIndex 84), (facetIndex 86), (facetIndex 88)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 10), (facetIndex 18), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 65), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 10), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 7), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 11), (facetIndex 19), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 53), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 7), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 0), (facetIndex 6), (facetIndex 10), (facetIndex 14), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 53), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 9), (facetIndex 15), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 62), (facetIndex 77), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 77), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 6), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 65), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 10), (facetIndex 14), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 53), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 0), (facetIndex 6), (facetIndex 10), (facetIndex 14), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 56), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 9), (facetIndex 15), (facetIndex 40), (facetIndex 45), (facetIndex 52), (facetIndex 57), (facetIndex 64), (facetIndex 77), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 77), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 6), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 52), (facetIndex 56), (facetIndex 65), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 10), (facetIndex 14), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 56), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 7), (facetIndex 16), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 56), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 6), (facetIndex 15), (facetIndex 16), (facetIndex 19), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 6), (facetIndex 14), (facetIndex 15), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 6), (facetIndex 14), (facetIndex 15), (facetIndex 18), (facetIndex 25), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 6), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 11), (facetIndex 15), (facetIndex 25), (facetIndex 32), (facetIndex 40), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leaf0027 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 6), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0027_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0027 = true := by
  decide +kernel
theorem leaf0027_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0027 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0027_counts_checked
def leaf0028 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 11), (facetIndex 16), (facetIndex 30), (facetIndex 35), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0028_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0028 = true := by
  decide +kernel
theorem leaf0028_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0028 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0028_counts_checked
def leaf0029 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 6), (facetIndex 17), (facetIndex 32), (facetIndex 39), (facetIndex 56), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0029_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0029 = true := by
  decide +kernel
theorem leaf0029_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0029 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0029_counts_checked
def leaf0030 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 9), (facetIndex 17), (facetIndex 35), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0030_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0030 = true := by
  decide +kernel
theorem leaf0030_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0030 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0030_counts_checked
def leaf0031 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 9), (facetIndex 17), (facetIndex 39), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 62), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0031_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0031 = true := by
  decide +kernel
theorem leaf0031_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0031 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0031_counts_checked
def leaf0032 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 6), (facetIndex 17), (facetIndex 32), (facetIndex 35), (facetIndex 45), (facetIndex 56), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0032_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0032 = true := by
  decide +kernel
theorem leaf0032_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0032 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0032_counts_checked
def leaf0033 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 11), (facetIndex 16), (facetIndex 25), (facetIndex 39), (facetIndex 41), (facetIndex 58), (facetIndex 62), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0033_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0033 = true := by
  decide +kernel
theorem leaf0033_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0033 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0033_counts_checked
def leaf0034 : List (Fin data.count) := [(facetIndex 7), (facetIndex 12), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 35), (facetIndex 41), (facetIndex 45), (facetIndex 50), (facetIndex 56), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0034_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0034 = true := by
  decide +kernel
theorem leaf0034_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0034 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0034_counts_checked
def leaf0035 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 50), (facetIndex 64), (facetIndex 77), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0035_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0035 = true := by
  decide +kernel
theorem leaf0035_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0035 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0035_counts_checked
def leaf0036 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 16), (facetIndex 19), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 50), (facetIndex 56), (facetIndex 62), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 91)]
theorem leaf0036_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0036 = true := by
  decide +kernel
theorem leaf0036_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0036 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0036_counts_checked
def leaf0037 : List (Fin data.count) := [(facetIndex 7), (facetIndex 12), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 50), (facetIndex 56), (facetIndex 62), (facetIndex 82), (facetIndex 83), (facetIndex 89), (facetIndex 91)]
theorem leaf0037_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0037 = true := by
  decide +kernel
theorem leaf0037_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0037 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0037_counts_checked
def leaf0038 : List (Fin data.count) := [(facetIndex 4), (facetIndex 7), (facetIndex 11), (facetIndex 13), (facetIndex 31), (facetIndex 35), (facetIndex 41), (facetIndex 50), (facetIndex 53), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0038_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0038 = true := by
  decide +kernel
theorem leaf0038_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0038 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0038_counts_checked
def leaf0039 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 50), (facetIndex 62), (facetIndex 77), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0039_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0039 = true := by
  decide +kernel
theorem leaf0039_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0039 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0039_counts_checked
def leaf0040 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 30), (facetIndex 35), (facetIndex 41), (facetIndex 50), (facetIndex 53), (facetIndex 77), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0040_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0040 = true := by
  decide +kernel
theorem leaf0040_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0040 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0040_counts_checked
def leaf0041 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 10), (facetIndex 17), (facetIndex 32), (facetIndex 39), (facetIndex 50), (facetIndex 56), (facetIndex 62), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 89), (facetIndex 91)]
theorem leaf0041_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0041 = true := by
  decide +kernel
theorem leaf0041_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0041 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0041_counts_checked
def leaf0042 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 7), (facetIndex 17), (facetIndex 35), (facetIndex 41), (facetIndex 45), (facetIndex 50), (facetIndex 56), (facetIndex 77), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0042_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0042 = true := by
  decide +kernel
theorem leaf0042_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0042 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0042_counts_checked
def leaf0043 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 7), (facetIndex 17), (facetIndex 39), (facetIndex 41), (facetIndex 50), (facetIndex 56), (facetIndex 62), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 89), (facetIndex 91)]
theorem leaf0043_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0043 = true := by
  decide +kernel
theorem leaf0043_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0043 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0043_counts_checked
def leaf0044 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 10), (facetIndex 17), (facetIndex 32), (facetIndex 35), (facetIndex 45), (facetIndex 50), (facetIndex 56), (facetIndex 77), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0044_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0044 = true := by
  decide +kernel
theorem leaf0044_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0044 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0044_counts_checked
def leaf0045 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 25), (facetIndex 39), (facetIndex 41), (facetIndex 50), (facetIndex 62), (facetIndex 77), (facetIndex 82), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0045_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0045 = true := by
  decide +kernel
theorem leaf0045_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0045 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0045_counts_checked
def leaf0046 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0046_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0046 = true := by
  decide +kernel
theorem leaf0046_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0046 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0046_counts_checked
def leaf0047 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 79), (facetIndex 85), (facetIndex 87)]
theorem leaf0047_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0047 = true := by
  decide +kernel
theorem leaf0047_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0047 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0047_counts_checked
def leaf0048 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 15), (facetIndex 18), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0048_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0048 = true := by
  decide +kernel
theorem leaf0048_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0048 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0048_counts_checked
def leaf0049 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 7), (facetIndex 17), (facetIndex 29), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0049_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0049 = true := by
  decide +kernel
theorem leaf0049_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0049 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0049_counts_checked
def leaf0050 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 11), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0050_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0050 = true := by
  decide +kernel
theorem leaf0050_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0050 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0050_counts_checked
def leaf0051 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 32), (facetIndex 38), (facetIndex 39), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0051_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0051 = true := by
  decide +kernel
theorem leaf0051_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0051 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0051_counts_checked
def leaf0052 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0052_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0052 = true := by
  decide +kernel
theorem leaf0052_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0052 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0052_counts_checked
def leaf0053 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0053_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0053 = true := by
  decide +kernel
theorem leaf0053_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0053 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0053_counts_checked
def leaf0054 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 84), (facetIndex 86), (facetIndex 90)]
theorem leaf0054_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0054 = true := by
  decide +kernel
theorem leaf0054_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0054 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0054_counts_checked
def leaf0055 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 79), (facetIndex 84), (facetIndex 86)]
theorem leaf0055_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0055 = true := by
  decide +kernel
theorem leaf0055_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0055 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0055_counts_checked
def leaf0056 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 15), (facetIndex 18), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 84), (facetIndex 86), (facetIndex 88)]
theorem leaf0056_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0056 = true := by
  decide +kernel
theorem leaf0056_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0056 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0056_counts_checked
def leaf0057 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 7), (facetIndex 17), (facetIndex 29), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 90)]
theorem leaf0057_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0057 = true := by
  decide +kernel
theorem leaf0057_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0057 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0057_counts_checked
def leaf0058 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 11), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 79), (facetIndex 84), (facetIndex 86), (facetIndex 88)]
theorem leaf0058_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0058 = true := by
  decide +kernel
theorem leaf0058_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0058 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0058_counts_checked
def leaf0059 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 32), (facetIndex 38), (facetIndex 39), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 79), (facetIndex 84), (facetIndex 86), (facetIndex 88)]
theorem leaf0059_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0059 = true := by
  decide +kernel
theorem leaf0059_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0059 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0059_counts_checked
def leaf0060 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 82), (facetIndex 84), (facetIndex 86)]
theorem leaf0060_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0060 = true := by
  decide +kernel
theorem leaf0060_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0060 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0060_counts_checked
def leaf0061 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 82), (facetIndex 84), (facetIndex 86)]
theorem leaf0061_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0061 = true := by
  decide +kernel
theorem leaf0061_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0061 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0061_counts_checked
def leaf0062 : List (Fin data.count) := [(facetIndex 7), (facetIndex 17), (facetIndex 18), (facetIndex 19), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 91)]
theorem leaf0062_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0062 = true := by
  decide +kernel
theorem leaf0062_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0062 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0062_counts_checked
def leaf0063 : List (Fin data.count) := [(facetIndex 7), (facetIndex 14), (facetIndex 17), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 91)]
theorem leaf0063_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0063 = true := by
  decide +kernel
theorem leaf0063_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0063 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0063_counts_checked
def leaf0064 : List (Fin data.count) := [(facetIndex 1), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 40), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 77), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0064_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0064 = true := by
  decide +kernel
theorem leaf0064_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0064 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0064_counts_checked
def leaf0065 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 91)]
theorem leaf0065_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0065 = true := by
  decide +kernel
theorem leaf0065_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0065 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0065_counts_checked
def leaf0066 : List (Fin data.count) := [(facetIndex 11), (facetIndex 13), (facetIndex 17), (facetIndex 19), (facetIndex 31), (facetIndex 38), (facetIndex 39), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0066_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0066 = true := by
  decide +kernel
theorem leaf0066_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0066 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0066_counts_checked
def leaf0067 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 17), (facetIndex 19), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0067_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0067 = true := by
  decide +kernel
theorem leaf0067_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0067 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0067_counts_checked
def leaf0068 : List (Fin data.count) := [(facetIndex 1), (facetIndex 15), (facetIndex 16), (facetIndex 17), (facetIndex 30), (facetIndex 40), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 77), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0068_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0068 = true := by
  decide +kernel
theorem leaf0068_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0068 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0068_counts_checked
def leaf0069 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 91)]
theorem leaf0069_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0069 = true := by
  decide +kernel
theorem leaf0069_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0069 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0069_counts_checked
def leaf0070 : List (Fin data.count) := [(facetIndex 4), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 40), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0070_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0070 = true := by
  decide +kernel
theorem leaf0070_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0070 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0070_counts_checked
def leaf0071 : List (Fin data.count) := [(facetIndex 1), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 30), (facetIndex 40), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0071_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0071 = true := by
  decide +kernel
theorem leaf0071_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0071 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0071_counts_checked
def leaf0072 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0072_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0072 = true := by
  decide +kernel
theorem leaf0072_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0072 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0072_counts_checked
def leaf0073 : List (Fin data.count) := [(facetIndex 7), (facetIndex 12), (facetIndex 16), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0073_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0073 = true := by
  decide +kernel
theorem leaf0073_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0073 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0073_counts_checked
def leaf0074 : List (Fin data.count) := [(facetIndex 7), (facetIndex 14), (facetIndex 16), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 91)]
theorem leaf0074_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0074 = true := by
  decide +kernel
theorem leaf0074_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0074 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0074_counts_checked
def leaf0075 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 7), (facetIndex 17), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0075_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0075 = true := by
  decide +kernel
theorem leaf0075_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0075 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0075_counts_checked
def leaf0076 : List (Fin data.count) := [(facetIndex 0), (facetIndex 4), (facetIndex 10), (facetIndex 17), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0076_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0076 = true := by
  decide +kernel
theorem leaf0076_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0076 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0076_counts_checked
def leaf0077 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 10), (facetIndex 17), (facetIndex 32), (facetIndex 39), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0077_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0077 = true := by
  decide +kernel
theorem leaf0077_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0077 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0077_counts_checked
def leaf0078 : List (Fin data.count) := [(facetIndex 0), (facetIndex 4), (facetIndex 10), (facetIndex 18), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0078_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0078 = true := by
  decide +kernel
theorem leaf0078_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0078 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0078_counts_checked
def leaf0079 : List (Fin data.count) := [(facetIndex 4), (facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 31), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0079_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0079 = true := by
  decide +kernel
theorem leaf0079_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0079 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0079_counts_checked
def leaf0080 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 10), (facetIndex 18), (facetIndex 30), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0080_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0080 = true := by
  decide +kernel
theorem leaf0080_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0080 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0080_counts_checked
def leaf0081 : List (Fin data.count) := [(facetIndex 4), (facetIndex 7), (facetIndex 11), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0081_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0081 = true := by
  decide +kernel
theorem leaf0081_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0081 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0081_counts_checked
def leaf0082 : List (Fin data.count) := [(facetIndex 7), (facetIndex 12), (facetIndex 16), (facetIndex 18), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0082_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0082 = true := by
  decide +kernel
theorem leaf0082_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0082 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0082_counts_checked
def leaf0083 : List (Fin data.count) := [(facetIndex 7), (facetIndex 12), (facetIndex 16), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0083_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0083 = true := by
  decide +kernel
theorem leaf0083_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0083 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0083_counts_checked
def leaf0084 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 18), (facetIndex 38), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0084_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0084 = true := by
  decide +kernel
theorem leaf0084_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0084 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0084_counts_checked
def leaf0085 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 7), (facetIndex 17), (facetIndex 29), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0085_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0085 = true := by
  decide +kernel
theorem leaf0085_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0085 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0085_counts_checked
def leaf0086 : List (Fin data.count) := [(facetIndex 0), (facetIndex 14), (facetIndex 15), (facetIndex 17), (facetIndex 29), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0086_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0086 = true := by
  decide +kernel
theorem leaf0086_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0086 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0086_counts_checked
def leaf0087 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 7), (facetIndex 17), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0087_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0087 = true := by
  decide +kernel
theorem leaf0087_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0087 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0087_counts_checked
def leaf0088 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 14), (facetIndex 17), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0088_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0088 = true := by
  decide +kernel
theorem leaf0088_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0088 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0088_counts_checked
def leaf0089 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 10), (facetIndex 17), (facetIndex 32), (facetIndex 37), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0089_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0089 = true := by
  decide +kernel
theorem leaf0089_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0089 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0089_counts_checked
def leaf0090 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 15), (facetIndex 18), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0090_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0090 = true := by
  decide +kernel
theorem leaf0090_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0090 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0090_counts_checked
def leaf0091 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0091_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0091 = true := by
  decide +kernel
theorem leaf0091_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0091 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0091_counts_checked
def leaf0092 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 15), (facetIndex 18), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0092_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0092 = true := by
  decide +kernel
theorem leaf0092_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0092 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0092_counts_checked
def leaf0093 : List (Fin data.count) := [(facetIndex 0), (facetIndex 12), (facetIndex 15), (facetIndex 18), (facetIndex 29), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0093_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0093 = true := by
  decide +kernel
theorem leaf0093_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0093 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0093_counts_checked
def leaf0094 : List (Fin data.count) := [(facetIndex 1), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 27), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0094_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0094 = true := by
  decide +kernel
theorem leaf0094_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0094 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0094_counts_checked
def leaf0095 : List (Fin data.count) := [(facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0095_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0095 = true := by
  decide +kernel
theorem leaf0095_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0095 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0095_counts_checked
def leaf0096 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 12), (facetIndex 18), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0096_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0096 = true := by
  decide +kernel
theorem leaf0096_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0096 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0096_counts_checked
def leaf0097 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 12), (facetIndex 18), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0097_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0097 = true := by
  decide +kernel
theorem leaf0097_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0097 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0097_counts_checked
def leaf0098 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 10), (facetIndex 18), (facetIndex 27), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0098_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0098 = true := by
  decide +kernel
theorem leaf0098_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0098 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0098_counts_checked
def leaf0099 : List (Fin data.count) := [(facetIndex 4), (facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0099_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0099 = true := by
  decide +kernel
theorem leaf0099_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0099 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0099_counts_checked
def leaf0100 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 11), (facetIndex 16), (facetIndex 38), (facetIndex 39), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0100_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0100 = true := by
  decide +kernel
theorem leaf0100_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0100 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0100_counts_checked
def leaf0101 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 32), (facetIndex 38), (facetIndex 39), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0101_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0101 = true := by
  decide +kernel
theorem leaf0101_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0101 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0101_counts_checked
def leaf0102 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 13), (facetIndex 16), (facetIndex 31), (facetIndex 38), (facetIndex 39), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0102_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0102 = true := by
  decide +kernel
theorem leaf0102_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0102 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0102_counts_checked
def leaf0103 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 30), (facetIndex 37), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0103_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0103 = true := by
  decide +kernel
theorem leaf0103_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0103 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0103_counts_checked
def leaf0104 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 12), (facetIndex 16), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0104_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0104 = true := by
  decide +kernel
theorem leaf0104_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0104 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0104_counts_checked
def leaf0105 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 27), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0105_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0105 = true := by
  decide +kernel
theorem leaf0105_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0105 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0105_counts_checked
def leaf0106 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 11), (facetIndex 15), (facetIndex 40), (facetIndex 45), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0106_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0106 = true := by
  decide +kernel
theorem leaf0106_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0106 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0106_counts_checked
def leaf0107 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 11), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0107_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0107 = true := by
  decide +kernel
theorem leaf0107_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0107 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0107_counts_checked
def leaf0108 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0108_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0108 = true := by
  decide +kernel
theorem leaf0108_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0108 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0108_counts_checked
def leaf0109 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 11), (facetIndex 12), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0109_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0109 = true := by
  decide +kernel
theorem leaf0109_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0109 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0109_counts_checked
def leaf0110 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 11), (facetIndex 14), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0110_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0110 = true := by
  decide +kernel
theorem leaf0110_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0110 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0110_counts_checked
def leaf0111 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 12), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0111_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0111 = true := by
  decide +kernel
theorem leaf0111_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0111 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0111_counts_checked
def leaf0112 : List (Fin data.count) := [(facetIndex 7), (facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0112_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0112 = true := by
  decide +kernel
theorem leaf0112_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0112 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0112_counts_checked
def leaf0113 : List (Fin data.count) := [(facetIndex 7), (facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0113_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0113 = true := by
  decide +kernel
theorem leaf0113_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0113 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0113_counts_checked
def leaf0114 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 7), (facetIndex 15), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0114_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0114 = true := by
  decide +kernel
theorem leaf0114_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0114 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0114_counts_checked
def leaf0115 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 7), (facetIndex 15), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0115_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0115 = true := by
  decide +kernel
theorem leaf0115_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0115 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0115_counts_checked
def leaf0116 : List (Fin data.count) := [(facetIndex 4), (facetIndex 13), (facetIndex 15), (facetIndex 16), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0116_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0116 = true := by
  decide +kernel
theorem leaf0116_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0116 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0116_counts_checked
def leaf0117 : List (Fin data.count) := [(facetIndex 0), (facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0117_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0117 = true := by
  decide +kernel
theorem leaf0117_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0117 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0117_counts_checked
def leaf0118 : List (Fin data.count) := [(facetIndex 5), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0118_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0118 = true := by
  decide +kernel
theorem leaf0118_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0118 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0118_counts_checked
def leaf0119 : List (Fin data.count) := [(facetIndex 0), (facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0119_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0119 = true := by
  decide +kernel
theorem leaf0119_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0119 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0119_counts_checked
def leaf0120 : List (Fin data.count) := [(facetIndex 11), (facetIndex 13), (facetIndex 15), (facetIndex 19), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 73), (facetIndex 81), (facetIndex 85), (facetIndex 87)]
theorem leaf0120_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0120 = true := by
  decide +kernel
theorem leaf0120_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0120 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0120_counts_checked
def leaf0121 : List (Fin data.count) := [(facetIndex 5), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 79), (facetIndex 85), (facetIndex 87)]
theorem leaf0121_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0121 = true := by
  decide +kernel
theorem leaf0121_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0121 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0121_counts_checked
def leaf0122 : List (Fin data.count) := [(facetIndex 0), (facetIndex 15), (facetIndex 17), (facetIndex 19), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87)]
theorem leaf0122_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0122 = true := by
  decide +kernel
theorem leaf0122_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0122 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0122_counts_checked
def leaf0123 : List (Fin data.count) := [(facetIndex 0), (facetIndex 15), (facetIndex 17), (facetIndex 19), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87)]
theorem leaf0123_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0123 = true := by
  decide +kernel
theorem leaf0123_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0123 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0123_counts_checked
def leaf0124 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 11), (facetIndex 17), (facetIndex 32), (facetIndex 35), (facetIndex 45), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0124_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0124 = true := by
  decide +kernel
theorem leaf0124_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0124 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0124_counts_checked
def leaf0125 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 11), (facetIndex 17), (facetIndex 32), (facetIndex 39), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0125_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0125 = true := by
  decide +kernel
theorem leaf0125_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0125 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0125_counts_checked
def leaf0126 : List (Fin data.count) := [(facetIndex 0), (facetIndex 8), (facetIndex 15), (facetIndex 18), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0126_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0126 = true := by
  decide +kernel
theorem leaf0126_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0126 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0126_counts_checked
def leaf0127 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 5), (facetIndex 17), (facetIndex 29), (facetIndex 41), (facetIndex 44), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0127_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0127 = true := by
  decide +kernel
theorem leaf0127_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0127 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0127_counts_checked
def leaf0128 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 11), (facetIndex 18), (facetIndex 32), (facetIndex 35), (facetIndex 45), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0128_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0128 = true := by
  decide +kernel
theorem leaf0128_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0128 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0128_counts_checked
def leaf0129 : List (Fin data.count) := [(facetIndex 0), (facetIndex 4), (facetIndex 11), (facetIndex 18), (facetIndex 32), (facetIndex 35), (facetIndex 38), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0129_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0129 = true := by
  decide +kernel
theorem leaf0129_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0129 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0129_counts_checked
def leaf0130 : List (Fin data.count) := [(facetIndex 0), (facetIndex 14), (facetIndex 15), (facetIndex 18), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0130_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0130 = true := by
  decide +kernel
theorem leaf0130_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0130 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0130_counts_checked
def leaf0131 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 17), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0131_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0131 = true := by
  decide +kernel
theorem leaf0131_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0131 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0131_counts_checked
def leaf0132 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 11), (facetIndex 16), (facetIndex 32), (facetIndex 39), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0132_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0132 = true := by
  decide +kernel
theorem leaf0132_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0132 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0132_counts_checked
def leaf0133 : List (Fin data.count) := [(facetIndex 0), (facetIndex 4), (facetIndex 11), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0133_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0133 = true := by
  decide +kernel
theorem leaf0133_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0133 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0133_counts_checked
def leaf0134 : List (Fin data.count) := [(facetIndex 0), (facetIndex 14), (facetIndex 15), (facetIndex 16), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0134_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0134 = true := by
  decide +kernel
theorem leaf0134_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0134 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0134_counts_checked
def leaf0135 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 16), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0135_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0135 = true := by
  decide +kernel
theorem leaf0135_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0135 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0135_counts_checked
def leaf0136 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 13), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0136_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0136 = true := by
  decide +kernel
theorem leaf0136_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0136 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0136_counts_checked
def leaf0137 : List (Fin data.count) := [(facetIndex 0), (facetIndex 8), (facetIndex 11), (facetIndex 15), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0137_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0137 = true := by
  decide +kernel
theorem leaf0137_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0137 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0137_counts_checked
def leaf0138 : List (Fin data.count) := [(facetIndex 0), (facetIndex 8), (facetIndex 11), (facetIndex 16), (facetIndex 32), (facetIndex 38), (facetIndex 39), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0138_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0138 = true := by
  decide +kernel
theorem leaf0138_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0138 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0138_counts_checked
def leaf0139 : List (Fin data.count) := [(facetIndex 0), (facetIndex 4), (facetIndex 15), (facetIndex 16), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0139_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0139 = true := by
  decide +kernel
theorem leaf0139_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0139 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0139_counts_checked
def leaf0140 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 13), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0140_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0140 = true := by
  decide +kernel
theorem leaf0140_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0140 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0140_counts_checked
def leaf0141 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 4), (facetIndex 16), (facetIndex 29), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0141_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0141 = true := by
  decide +kernel
theorem leaf0141_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0141 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0141_counts_checked
def leaf0142 : List (Fin data.count) := [(facetIndex 1), (facetIndex 11), (facetIndex 16), (facetIndex 18), (facetIndex 25), (facetIndex 39), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0142_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0142 = true := by
  decide +kernel
theorem leaf0142_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0142 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0142_counts_checked
def leaf0143 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 19), (facetIndex 25), (facetIndex 29), (facetIndex 39), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0143_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0143 = true := by
  decide +kernel
theorem leaf0143_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0143 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0143_counts_checked
def leaf0144 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 16), (facetIndex 18), (facetIndex 25), (facetIndex 29), (facetIndex 39), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0144_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0144 = true := by
  decide +kernel
theorem leaf0144_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0144 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0144_counts_checked
def leaf0145 : List (Fin data.count) := [(facetIndex 11), (facetIndex 13), (facetIndex 18), (facetIndex 19), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0145_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0145 = true := by
  decide +kernel
theorem leaf0145_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0145 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0145_counts_checked
def leaf0146 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 13), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0146_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0146 = true := by
  decide +kernel
theorem leaf0146_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0146 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0146_counts_checked
def leaf0147 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 11), (facetIndex 18), (facetIndex 39), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0147_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0147 = true := by
  decide +kernel
theorem leaf0147_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0147 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0147_counts_checked
def leaf0148 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 17), (facetIndex 18), (facetIndex 39), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0148_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0148 = true := by
  decide +kernel
theorem leaf0148_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0148 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0148_counts_checked
def leaf0149 : List (Fin data.count) := [(facetIndex 0), (facetIndex 12), (facetIndex 17), (facetIndex 18), (facetIndex 29), (facetIndex 39), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0149_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0149 = true := by
  decide +kernel
theorem leaf0149_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0149 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0149_counts_checked
def leaf0150 : List (Fin data.count) := [(facetIndex 1), (facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 27), (facetIndex 39), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0150_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0150 = true := by
  decide +kernel
theorem leaf0150_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0150 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0150_counts_checked
def leaf0151 : List (Fin data.count) := [(facetIndex 12), (facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0151_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0151 = true := by
  decide +kernel
theorem leaf0151_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0151 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0151_counts_checked
def leaf0152 : List (Fin data.count) := [(facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 19), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0152_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0152 = true := by
  decide +kernel
theorem leaf0152_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0152 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0152_counts_checked
def leaf0153 : List (Fin data.count) := [(facetIndex 0), (facetIndex 16), (facetIndex 18), (facetIndex 19), (facetIndex 29), (facetIndex 39), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0153_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0153 = true := by
  decide +kernel
theorem leaf0153_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0153 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0153_counts_checked
def leaf0154 : List (Fin data.count) := [(facetIndex 5), (facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0154_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0154 = true := by
  decide +kernel
theorem leaf0154_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0154 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0154_counts_checked
def leaf0155 : List (Fin data.count) := [(facetIndex 5), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0155_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0155 = true := by
  decide +kernel
theorem leaf0155_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0155 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0155_counts_checked
def leaf0156 : List (Fin data.count) := [(facetIndex 1), (facetIndex 16), (facetIndex 17), (facetIndex 18), (facetIndex 25), (facetIndex 39), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 69), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0156_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0156 = true := by
  decide +kernel
theorem leaf0156_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0156 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0156_counts_checked
def leaf0157 : List (Fin data.count) := [(facetIndex 1), (facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 25), (facetIndex 39), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0157_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0157 = true := by
  decide +kernel
theorem leaf0157_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0157 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0157_counts_checked
def leaf0158 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 7), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0158_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0158 = true := by
  decide +kernel
theorem leaf0158_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0158 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0158_counts_checked
def leaf0159 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 7), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0159_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0159 = true := by
  decide +kernel
theorem leaf0159_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0159 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0159_counts_checked
def leaf0160 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 7), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 90)]
theorem leaf0160_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0160 = true := by
  decide +kernel
theorem leaf0160_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0160 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0160_counts_checked
def leaf0161 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 7), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 90)]
theorem leaf0161_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0161 = true := by
  decide +kernel
theorem leaf0161_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0161 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0161_counts_checked
def leaf0162 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 9), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0162_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0162 = true := by
  decide +kernel
theorem leaf0162_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0162 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0162_counts_checked
def leaf0163 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 9), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 57), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0163_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0163 = true := by
  decide +kernel
theorem leaf0163_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0163 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0163_counts_checked
def leaf0164 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0164_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0164 = true := by
  decide +kernel
theorem leaf0164_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0164 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0164_counts_checked
def leaf0165 : List (Fin data.count) := [(facetIndex 9), (facetIndex 10), (facetIndex 11), (facetIndex 19), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 62), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0165_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0165 = true := by
  decide +kernel
theorem leaf0165_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0165 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0165_counts_checked
def leaf0166 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 18), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0166_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0166 = true := by
  decide +kernel
theorem leaf0166_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0166 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0166_counts_checked
def leaf0167 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 9), (facetIndex 12), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0167_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0167 = true := by
  decide +kernel
theorem leaf0167_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0167 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0167_counts_checked
def leaf0168 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 6), (facetIndex 13), (facetIndex 31), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0168_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0168 = true := by
  decide +kernel
theorem leaf0168_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0168 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0168_counts_checked
def leaf0169 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 7), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0169_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0169 = true := by
  decide +kernel
theorem leaf0169_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0169 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0169_counts_checked
def leaf0170 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 62), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0170_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0170 = true := by
  decide +kernel
theorem leaf0170_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0170 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0170_counts_checked
def leaf0171 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 7), (facetIndex 14), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0171_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0171 = true := by
  decide +kernel
theorem leaf0171_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0171 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0171_counts_checked
def leaf0172 : List (Fin data.count) := [(facetIndex 7), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0172_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0172 = true := by
  decide +kernel
theorem leaf0172_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0172 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0172_counts_checked
def leaf0173 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 9), (facetIndex 12), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0173_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0173 = true := by
  decide +kernel
theorem leaf0173_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0173 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0173_counts_checked
def leaf0174 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 6), (facetIndex 13), (facetIndex 31), (facetIndex 45), (facetIndex 52), (facetIndex 56), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0174_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0174 = true := by
  decide +kernel
theorem leaf0174_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0174 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0174_counts_checked
def leaf0175 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 7), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0175_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0175 = true := by
  decide +kernel
theorem leaf0175_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0175 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0175_counts_checked
def leaf0176 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 52), (facetIndex 57), (facetIndex 64), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0176_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0176 = true := by
  decide +kernel
theorem leaf0176_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0176 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0176_counts_checked
def leaf0177 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 7), (facetIndex 14), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0177_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0177 = true := by
  decide +kernel
theorem leaf0177_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0177 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0177_counts_checked
def leaf0178 : List (Fin data.count) := [(facetIndex 7), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0178_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0178 = true := by
  decide +kernel
theorem leaf0178_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0178 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0178_counts_checked
def leaf0179 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 16), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 64), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0179_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0179 = true := by
  decide +kernel
theorem leaf0179_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0179 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0179_counts_checked
def leaf0180 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 16), (facetIndex 19), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 62), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0180_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0180 = true := by
  decide +kernel
theorem leaf0180_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0180 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0180_counts_checked
def leaf0181 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 62), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0181_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0181 = true := by
  decide +kernel
theorem leaf0181_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0181 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0181_counts_checked
def leaf0182 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 35), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0182_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0182 = true := by
  decide +kernel
theorem leaf0182_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0182 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0182_counts_checked
def leaf0183 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 9), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0183_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0183 = true := by
  decide +kernel
theorem leaf0183_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0183 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0183_counts_checked
def leaf0184 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 11), (facetIndex 13), (facetIndex 31), (facetIndex 35), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0184_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0184 = true := by
  decide +kernel
theorem leaf0184_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0184 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0184_counts_checked
def leaf0185 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 9), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 58), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0185_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0185 = true := by
  decide +kernel
theorem leaf0185_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0185 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0185_counts_checked
def leaf0186 : List (Fin data.count) := [(facetIndex 3), (facetIndex 6), (facetIndex 11), (facetIndex 16), (facetIndex 25), (facetIndex 32), (facetIndex 39), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0186_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0186 = true := by
  decide +kernel
theorem leaf0186_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0186 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0186_counts_checked
def leaf0187 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 9), (facetIndex 18), (facetIndex 30), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 64), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0187_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0187 = true := by
  decide +kernel
theorem leaf0187_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0187 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0187_counts_checked
def leaf0188 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 6), (facetIndex 18), (facetIndex 25), (facetIndex 32), (facetIndex 45), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0188_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0188 = true := by
  decide +kernel
theorem leaf0188_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0188 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0188_counts_checked
def leaf0189 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 6), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0189_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0189 = true := by
  decide +kernel
theorem leaf0189_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0189 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0189_counts_checked
def leaf0190 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 9), (facetIndex 18), (facetIndex 25), (facetIndex 41), (facetIndex 45), (facetIndex 58), (facetIndex 64), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0190_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0190 = true := by
  decide +kernel
theorem leaf0190_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0190 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0190_counts_checked
def leaf0191 : List (Fin data.count) := [(facetIndex 3), (facetIndex 6), (facetIndex 11), (facetIndex 16), (facetIndex 30), (facetIndex 32), (facetIndex 35), (facetIndex 53), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0191_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0191 = true := by
  decide +kernel
theorem leaf0191_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0191 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0191_counts_checked
def leaf0192 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 15), (facetIndex 18), (facetIndex 25), (facetIndex 32), (facetIndex 40), (facetIndex 45), (facetIndex 50), (facetIndex 64), (facetIndex 77), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0192_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0192 = true := by
  decide +kernel
theorem leaf0192_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0192 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0192_counts_checked
def leaf0193 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 8), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 50), (facetIndex 56), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0193_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0193 = true := by
  decide +kernel
theorem leaf0193_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0193 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0193_counts_checked
def leaf0194 : List (Fin data.count) := [(facetIndex 10), (facetIndex 15), (facetIndex 16), (facetIndex 19), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 77), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0194_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0194 = true := by
  decide +kernel
theorem leaf0194_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0194 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0194_counts_checked
def leaf0195 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 15), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 77), (facetIndex 83), (facetIndex 89), (facetIndex 91)]
theorem leaf0195_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0195 = true := by
  decide +kernel
theorem leaf0195_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0195 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0195_counts_checked
def leaf0196 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 11), (facetIndex 15), (facetIndex 25), (facetIndex 32), (facetIndex 40), (facetIndex 50), (facetIndex 62), (facetIndex 77), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0196_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0196 = true := by
  decide +kernel
theorem leaf0196_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0196 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0196_counts_checked
def leaf0197 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 8), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 50), (facetIndex 53), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0197_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0197 = true := by
  decide +kernel
theorem leaf0197_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0197 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0197_counts_checked
def leaf0198 : List (Fin data.count) := [(facetIndex 3), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 25), (facetIndex 32), (facetIndex 39), (facetIndex 50), (facetIndex 62), (facetIndex 77), (facetIndex 82), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0198_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0198 = true := by
  decide +kernel
theorem leaf0198_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0198 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0198_counts_checked
def leaf0199 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 7), (facetIndex 18), (facetIndex 30), (facetIndex 41), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 89), (facetIndex 91)]
theorem leaf0199_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0199 = true := by
  decide +kernel
theorem leaf0199_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0199 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0199_counts_checked
def leaf0200 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 10), (facetIndex 18), (facetIndex 25), (facetIndex 32), (facetIndex 45), (facetIndex 50), (facetIndex 64), (facetIndex 77), (facetIndex 82), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0200_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0200 = true := by
  decide +kernel
theorem leaf0200_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0200 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0200_counts_checked
def leaf0201 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 10), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 89), (facetIndex 91)]
theorem leaf0201_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0201 = true := by
  decide +kernel
theorem leaf0201_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0201 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0201_counts_checked
def leaf0202 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 7), (facetIndex 18), (facetIndex 25), (facetIndex 41), (facetIndex 45), (facetIndex 50), (facetIndex 64), (facetIndex 77), (facetIndex 82), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0202_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0202 = true := by
  decide +kernel
theorem leaf0202_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0202 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0202_counts_checked
def leaf0203 : List (Fin data.count) := [(facetIndex 3), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 30), (facetIndex 32), (facetIndex 35), (facetIndex 50), (facetIndex 53), (facetIndex 77), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0203_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0203 = true := by
  decide +kernel
theorem leaf0203_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0203 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0203_counts_checked
def leaf0204 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0204_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0204 = true := by
  decide +kernel
theorem leaf0204_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0204 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0204_counts_checked
def leaf0205 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 81), (facetIndex 85), (facetIndex 87)]
theorem leaf0205_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0205 = true := by
  decide +kernel
theorem leaf0205_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0205 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0205_counts_checked
def leaf0206 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0206_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0206 = true := by
  decide +kernel
theorem leaf0206_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0206 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0206_counts_checked
def leaf0207 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 10), (facetIndex 18), (facetIndex 32), (facetIndex 38), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0207_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0207 = true := by
  decide +kernel
theorem leaf0207_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0207 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0207_counts_checked
def leaf0208 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0208_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0208 = true := by
  decide +kernel
theorem leaf0208_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0208 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0208_counts_checked
def leaf0209 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 29), (facetIndex 30), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0209_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0209 = true := by
  decide +kernel
theorem leaf0209_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0209 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0209_counts_checked
def leaf0210 : List (Fin data.count) := [(facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87)]
theorem leaf0210_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0210 = true := by
  decide +kernel
theorem leaf0210_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0210 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0210_counts_checked
def leaf0211 : List (Fin data.count) := [(facetIndex 10), (facetIndex 15), (facetIndex 16), (facetIndex 17), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87)]
theorem leaf0211_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0211 = true := by
  decide +kernel
theorem leaf0211_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0211 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0211_counts_checked
def leaf0212 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 81), (facetIndex 84), (facetIndex 86), (facetIndex 88)]
theorem leaf0212_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0212 = true := by
  decide +kernel
theorem leaf0212_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0212 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0212_counts_checked
def leaf0213 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 81), (facetIndex 84), (facetIndex 86)]
theorem leaf0213_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0213 = true := by
  decide +kernel
theorem leaf0213_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0213 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0213_counts_checked
def leaf0214 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 90)]
theorem leaf0214_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0214 = true := by
  decide +kernel
theorem leaf0214_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0214 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0214_counts_checked
def leaf0215 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 10), (facetIndex 18), (facetIndex 32), (facetIndex 38), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 84), (facetIndex 86), (facetIndex 88)]
theorem leaf0215_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0215 = true := by
  decide +kernel
theorem leaf0215_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0215 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0215_counts_checked
def leaf0216 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 90)]
theorem leaf0216_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0216 = true := by
  decide +kernel
theorem leaf0216_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0216 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0216_counts_checked
def leaf0217 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 29), (facetIndex 30), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 90)]
theorem leaf0217_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0217 = true := by
  decide +kernel
theorem leaf0217_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0217 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0217_counts_checked
def leaf0218 : List (Fin data.count) := [(facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 77), (facetIndex 81), (facetIndex 84), (facetIndex 86)]
theorem leaf0218_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0218 = true := by
  decide +kernel
theorem leaf0218_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0218 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0218_counts_checked
def leaf0219 : List (Fin data.count) := [(facetIndex 10), (facetIndex 15), (facetIndex 16), (facetIndex 17), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 77), (facetIndex 79), (facetIndex 84), (facetIndex 86)]
theorem leaf0219_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0219 = true := by
  decide +kernel
theorem leaf0219_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0219 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0219_counts_checked
def leaf0220 : List (Fin data.count) := [(facetIndex 10), (facetIndex 17), (facetIndex 18), (facetIndex 19), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0220_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0220 = true := by
  decide +kernel
theorem leaf0220_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0220 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0220_counts_checked
def leaf0221 : List (Fin data.count) := [(facetIndex 10), (facetIndex 12), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0221_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0221 = true := by
  decide +kernel
theorem leaf0221_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0221 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0221_counts_checked
def leaf0222 : List (Fin data.count) := [(facetIndex 3), (facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 91)]
theorem leaf0222_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0222 = true := by
  decide +kernel
theorem leaf0222_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0222 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0222_counts_checked
def leaf0223 : List (Fin data.count) := [(facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 77), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0223_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0223 = true := by
  decide +kernel
theorem leaf0223_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0223 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0223_counts_checked
def leaf0224 : List (Fin data.count) := [(facetIndex 11), (facetIndex 15), (facetIndex 18), (facetIndex 19), (facetIndex 29), (facetIndex 30), (facetIndex 40), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0224_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0224 = true := by
  decide +kernel
theorem leaf0224_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0224 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0224_counts_checked
def leaf0225 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 18), (facetIndex 19), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0225_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0225 = true := by
  decide +kernel
theorem leaf0225_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0225 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0225_counts_checked
def leaf0226 : List (Fin data.count) := [(facetIndex 3), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 31), (facetIndex 39), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 91)]
theorem leaf0226_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0226 = true := by
  decide +kernel
theorem leaf0226_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0226 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0226_counts_checked
def leaf0227 : List (Fin data.count) := [(facetIndex 10), (facetIndex 15), (facetIndex 16), (facetIndex 17), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 77), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0227_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0227 = true := by
  decide +kernel
theorem leaf0227_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0227 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0227_counts_checked
def leaf0228 : List (Fin data.count) := [(facetIndex 4), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 31), (facetIndex 40), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0228_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0228 = true := by
  decide +kernel
theorem leaf0228_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0228 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0228_counts_checked
def leaf0229 : List (Fin data.count) := [(facetIndex 3), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0229_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0229 = true := by
  decide +kernel
theorem leaf0229_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0229 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0229_counts_checked
def leaf0230 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0230_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0230 = true := by
  decide +kernel
theorem leaf0230_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0230 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0230_counts_checked
def leaf0231 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 16), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 91)]
theorem leaf0231_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0231 = true := by
  decide +kernel
theorem leaf0231_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0231 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0231_counts_checked
def leaf0232 : List (Fin data.count) := [(facetIndex 10), (facetIndex 12), (facetIndex 16), (facetIndex 17), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0232_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0232 = true := by
  decide +kernel
theorem leaf0232_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0232 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0232_counts_checked
def leaf0233 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 10), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0233_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0233 = true := by
  decide +kernel
theorem leaf0233_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0233 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0233_counts_checked
def leaf0234 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 7), (facetIndex 18), (facetIndex 31), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0234_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0234 = true := by
  decide +kernel
theorem leaf0234_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0234 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0234_counts_checked
def leaf0235 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 7), (facetIndex 18), (facetIndex 30), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0235_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0235 = true := by
  decide +kernel
theorem leaf0235_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0235 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0235_counts_checked
def leaf0236 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 7), (facetIndex 17), (facetIndex 31), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0236_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0236 = true := by
  decide +kernel
theorem leaf0236_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0236 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0236_counts_checked
def leaf0237 : List (Fin data.count) := [(facetIndex 4), (facetIndex 7), (facetIndex 10), (facetIndex 18), (facetIndex 31), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 73), (facetIndex 81), (facetIndex 89), (facetIndex 91)]
theorem leaf0237_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0237 = true := by
  decide +kernel
theorem leaf0237_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0237 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0237_counts_checked
def leaf0238 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 31), (facetIndex 39), (facetIndex 57), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 79), (facetIndex 89), (facetIndex 91)]
theorem leaf0238_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0238 = true := by
  decide +kernel
theorem leaf0238_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0238 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0238_counts_checked
def leaf0239 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 11), (facetIndex 18), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0239_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0239 = true := by
  decide +kernel
theorem leaf0239_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0239 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0239_counts_checked
def leaf0240 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 16), (facetIndex 17), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0240_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0240 = true := by
  decide +kernel
theorem leaf0240_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0240 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0240_counts_checked
def leaf0241 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 16), (facetIndex 18), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0241_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0241 = true := by
  decide +kernel
theorem leaf0241_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0241 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0241_counts_checked
def leaf0242 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 3), (facetIndex 17), (facetIndex 29), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0242_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0242 = true := by
  decide +kernel
theorem leaf0242_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0242 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0242_counts_checked
def leaf0243 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 10), (facetIndex 18), (facetIndex 32), (facetIndex 38), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0243_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0243 = true := by
  decide +kernel
theorem leaf0243_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0243 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0243_counts_checked
def leaf0244 : List (Fin data.count) := [(facetIndex 2), (facetIndex 12), (facetIndex 13), (facetIndex 18), (facetIndex 31), (facetIndex 38), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0244_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0244 = true := by
  decide +kernel
theorem leaf0244_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0244 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0244_counts_checked
def leaf0245 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 10), (facetIndex 18), (facetIndex 27), (facetIndex 32), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0245_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0245 = true := by
  decide +kernel
theorem leaf0245_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0245 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0245_counts_checked
def leaf0246 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 12), (facetIndex 18), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0246_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0246 = true := by
  decide +kernel
theorem leaf0246_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0246 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0246_counts_checked
def leaf0247 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 7), (facetIndex 18), (facetIndex 27), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0247_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0247 = true := by
  decide +kernel
theorem leaf0247_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0247 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0247_counts_checked
def leaf0248 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0248_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0248 = true := by
  decide +kernel
theorem leaf0248_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0248 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0248_counts_checked
def leaf0249 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 81), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0249_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0249 = true := by
  decide +kernel
theorem leaf0249_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0249 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0249_counts_checked
def leaf0250 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0250_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0250 = true := by
  decide +kernel
theorem leaf0250_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0250 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0250_counts_checked
def leaf0251 : List (Fin data.count) := [(facetIndex 2), (facetIndex 13), (facetIndex 14), (facetIndex 17), (facetIndex 31), (facetIndex 38), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0251_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0251 = true := by
  decide +kernel
theorem leaf0251_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0251 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0251_counts_checked
def leaf0252 : List (Fin data.count) := [(facetIndex 3), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0252_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0252 = true := by
  decide +kernel
theorem leaf0252_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0252 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0252_counts_checked
def leaf0253 : List (Fin data.count) := [(facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0253_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0253 = true := by
  decide +kernel
theorem leaf0253_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0253 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0253_counts_checked
def leaf0254 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 14), (facetIndex 17), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0254_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0254 = true := by
  decide +kernel
theorem leaf0254_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0254 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0254_counts_checked
def leaf0255 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 14), (facetIndex 17), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0255_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0255 = true := by
  decide +kernel
theorem leaf0255_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0255 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0255_counts_checked
def leaf0256 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 31), (facetIndex 37), (facetIndex 44), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 76), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0256_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0256 = true := by
  decide +kernel
theorem leaf0256_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0256 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0256_counts_checked
def leaf0257 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0257_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0257 = true := by
  decide +kernel
theorem leaf0257_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0257 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0257_counts_checked
def leaf0258 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 11), (facetIndex 16), (facetIndex 29), (facetIndex 30), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0258_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0258 = true := by
  decide +kernel
theorem leaf0258_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0258 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0258_counts_checked
def leaf0259 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 29), (facetIndex 30), (facetIndex 41), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0259_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0259 = true := by
  decide +kernel
theorem leaf0259_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0259 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0259_counts_checked
def leaf0260 : List (Fin data.count) := [(facetIndex 11), (facetIndex 14), (facetIndex 15), (facetIndex 16), (facetIndex 29), (facetIndex 30), (facetIndex 40), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0260_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0260 = true := by
  decide +kernel
theorem leaf0260_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0260 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0260_counts_checked
def leaf0261 : List (Fin data.count) := [(facetIndex 3), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 27), (facetIndex 32), (facetIndex 39), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0261_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0261 = true := by
  decide +kernel
theorem leaf0261_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0261 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0261_counts_checked
def leaf0262 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 14), (facetIndex 16), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0262_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0262 = true := by
  decide +kernel
theorem leaf0262_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0262 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0262_counts_checked
def leaf0263 : List (Fin data.count) := [(facetIndex 3), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 30), (facetIndex 32), (facetIndex 37), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0263_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0263 = true := by
  decide +kernel
theorem leaf0263_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0263 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0263_counts_checked
def leaf0264 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 11), (facetIndex 13), (facetIndex 31), (facetIndex 45), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0264_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0264 = true := by
  decide +kernel
theorem leaf0264_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0264 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0264_counts_checked
def leaf0265 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0265_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0265 = true := by
  decide +kernel
theorem leaf0265_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0265 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0265_counts_checked
def leaf0266 : List (Fin data.count) := [(facetIndex 11), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 52), (facetIndex 57), (facetIndex 65), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0266_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0266 = true := by
  decide +kernel
theorem leaf0266_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0266 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0266_counts_checked
def leaf0267 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 14), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0267_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0267 = true := by
  decide +kernel
theorem leaf0267_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0267 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0267_counts_checked
def leaf0268 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 12), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 79), (facetIndex 88), (facetIndex 89), (facetIndex 91)]
theorem leaf0268_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0268 = true := by
  decide +kernel
theorem leaf0268_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0268 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0268_counts_checked
def leaf0269 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 14), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 57), (facetIndex 65), (facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 90), (facetIndex 91)]
theorem leaf0269_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0269 = true := by
  decide +kernel
theorem leaf0269_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0269 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0269_counts_checked
def leaf0270 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0270_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0270 = true := by
  decide +kernel
theorem leaf0270_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0270 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0270_counts_checked
def leaf0271 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0271_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0271 = true := by
  decide +kernel
theorem leaf0271_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0271 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0271_counts_checked
def leaf0272 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 10), (facetIndex 13), (facetIndex 31), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0272_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0272 = true := by
  decide +kernel
theorem leaf0272_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0272 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0272_counts_checked
def leaf0273 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 10), (facetIndex 13), (facetIndex 31), (facetIndex 44), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0273_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0273 = true := by
  decide +kernel
theorem leaf0273_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0273 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0273_counts_checked
def leaf0274 : List (Fin data.count) := [(facetIndex 4), (facetIndex 13), (facetIndex 15), (facetIndex 16), (facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0274_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0274 = true := by
  decide +kernel
theorem leaf0274_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0274 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0274_counts_checked
def leaf0275 : List (Fin data.count) := [(facetIndex 2), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0275_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0275 = true := by
  decide +kernel
theorem leaf0275_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0275 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0275_counts_checked
def leaf0276 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 66), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0276_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0276 = true := by
  decide +kernel
theorem leaf0276_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0276 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0276_counts_checked
def leaf0277 : List (Fin data.count) := [(facetIndex 2), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0277_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0277 = true := by
  decide +kernel
theorem leaf0277_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0277 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0277_counts_checked
def leaf0278 : List (Fin data.count) := [(facetIndex 11), (facetIndex 13), (facetIndex 15), (facetIndex 19), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 79), (facetIndex 85), (facetIndex 87)]
theorem leaf0278_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0278 = true := by
  decide +kernel
theorem leaf0278_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0278 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0278_counts_checked
def leaf0279 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 66), (facetIndex 69), (facetIndex 73), (facetIndex 81), (facetIndex 85), (facetIndex 87)]
theorem leaf0279_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0279 = true := by
  decide +kernel
theorem leaf0279_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0279 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0279_counts_checked
def leaf0280 : List (Fin data.count) := [(facetIndex 2), (facetIndex 13), (facetIndex 18), (facetIndex 19), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0280_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0280 = true := by
  decide +kernel
theorem leaf0280_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0280 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0280_counts_checked
def leaf0281 : List (Fin data.count) := [(facetIndex 2), (facetIndex 13), (facetIndex 18), (facetIndex 19), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0281_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0281 = true := by
  decide +kernel
theorem leaf0281_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0281 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0281_counts_checked
def leaf0282 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 11), (facetIndex 18), (facetIndex 25), (facetIndex 41), (facetIndex 45), (facetIndex 58), (facetIndex 65), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0282_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0282 = true := by
  decide +kernel
theorem leaf0282_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0282 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0282_counts_checked
def leaf0283 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 11), (facetIndex 18), (facetIndex 30), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0283_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0283 = true := by
  decide +kernel
theorem leaf0283_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0283 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0283_counts_checked
def leaf0284 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0284_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0284 = true := by
  decide +kernel
theorem leaf0284_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0284 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0284_counts_checked
def leaf0285 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 8), (facetIndex 18), (facetIndex 32), (facetIndex 38), (facetIndex 44), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0285_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0285 = true := by
  decide +kernel
theorem leaf0285_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0285 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0285_counts_checked
def leaf0286 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 11), (facetIndex 17), (facetIndex 25), (facetIndex 41), (facetIndex 45), (facetIndex 58), (facetIndex 65), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0286_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0286 = true := by
  decide +kernel
theorem leaf0286_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0286 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0286_counts_checked
def leaf0287 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 11), (facetIndex 17), (facetIndex 25), (facetIndex 29), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0287_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0287 = true := by
  decide +kernel
theorem leaf0287_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0287 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0287_counts_checked
def leaf0288 : List (Fin data.count) := [(facetIndex 2), (facetIndex 12), (facetIndex 13), (facetIndex 17), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0288_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0288 = true := by
  decide +kernel
theorem leaf0288_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0288 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0288_counts_checked
def leaf0289 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 3), (facetIndex 18), (facetIndex 32), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0289_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0289 = true := by
  decide +kernel
theorem leaf0289_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0289 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0289_counts_checked
def leaf0290 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 11), (facetIndex 16), (facetIndex 30), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0290_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0290 = true := by
  decide +kernel
theorem leaf0290_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0290 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0290_counts_checked
def leaf0291 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 11), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 76), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0291_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0291 = true := by
  decide +kernel
theorem leaf0291_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0291 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0291_counts_checked
def leaf0292 : List (Fin data.count) := [(facetIndex 2), (facetIndex 12), (facetIndex 13), (facetIndex 16), (facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0292_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0292 = true := by
  decide +kernel
theorem leaf0292_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0292 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0292_counts_checked
def leaf0293 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 3), (facetIndex 16), (facetIndex 32), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0293_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0293 = true := by
  decide +kernel
theorem leaf0293_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0293 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0293_counts_checked
def leaf0294 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 3), (facetIndex 15), (facetIndex 32), (facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0294_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0294 = true := by
  decide +kernel
theorem leaf0294_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0294 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0294_counts_checked
def leaf0295 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 11), (facetIndex 13), (facetIndex 31), (facetIndex 41), (facetIndex 45), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0295_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0295 = true := by
  decide +kernel
theorem leaf0295_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0295 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0295_counts_checked
def leaf0296 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 11), (facetIndex 16), (facetIndex 29), (facetIndex 30), (facetIndex 41), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0296_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0296 = true := by
  decide +kernel
theorem leaf0296_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0296 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0296_counts_checked
def leaf0297 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 13), (facetIndex 16), (facetIndex 31), (facetIndex 41), (facetIndex 56), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0297_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0297 = true := by
  decide +kernel
theorem leaf0297_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0297 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0297_counts_checked
def leaf0298 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 3), (facetIndex 15), (facetIndex 32), (facetIndex 45), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0298_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0298 = true := by
  decide +kernel
theorem leaf0298_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0298 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0298_counts_checked
def leaf0299 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 4), (facetIndex 16), (facetIndex 32), (facetIndex 38), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0299_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0299 = true := by
  decide +kernel
theorem leaf0299_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0299 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0299_counts_checked
def leaf0300 : List (Fin data.count) := [(facetIndex 3), (facetIndex 11), (facetIndex 16), (facetIndex 17), (facetIndex 30), (facetIndex 32), (facetIndex 35), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0300_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0300 = true := by
  decide +kernel
theorem leaf0300_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0300 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0300_counts_checked
def leaf0301 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 19), (facetIndex 30), (facetIndex 32), (facetIndex 35), (facetIndex 38), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87)]
theorem leaf0301_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0301 = true := by
  decide +kernel
theorem leaf0301_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0301 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0301_counts_checked
def leaf0302 : List (Fin data.count) := [(facetIndex 11), (facetIndex 14), (facetIndex 16), (facetIndex 17), (facetIndex 30), (facetIndex 32), (facetIndex 35), (facetIndex 38), (facetIndex 57), (facetIndex 66), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 90)]
theorem leaf0302_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0302 = true := by
  decide +kernel
theorem leaf0302_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0302 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0302_counts_checked
def leaf0303 : List (Fin data.count) := [(facetIndex 11), (facetIndex 15), (facetIndex 17), (facetIndex 19), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87)]
theorem leaf0303_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0303 = true := by
  decide +kernel
theorem leaf0303_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0303 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0303_counts_checked
def leaf0304 : List (Fin data.count) := [(facetIndex 11), (facetIndex 14), (facetIndex 15), (facetIndex 17), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0304_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0304 = true := by
  decide +kernel
theorem leaf0304_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0304 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0304_counts_checked
def leaf0305 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 11), (facetIndex 17), (facetIndex 30), (facetIndex 32), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0305_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0305 = true := by
  decide +kernel
theorem leaf0305_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0305 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0305_counts_checked
def leaf0306 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0306_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0306 = true := by
  decide +kernel
theorem leaf0306_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0306 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0306_counts_checked
def leaf0307 : List (Fin data.count) := [(facetIndex 2), (facetIndex 14), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 38), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0307_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0307 = true := by
  decide +kernel
theorem leaf0307_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0307 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0307_counts_checked
def leaf0308 : List (Fin data.count) := [(facetIndex 3), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 37), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0308_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0308 = true := by
  decide +kernel
theorem leaf0308_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0308 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0308_counts_checked
def leaf0309 : List (Fin data.count) := [(facetIndex 14), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 83), (facetIndex 85), (facetIndex 87)]
theorem leaf0309_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0309 = true := by
  decide +kernel
theorem leaf0309_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0309 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0309_counts_checked
def leaf0310 : List (Fin data.count) := [(facetIndex 15), (facetIndex 16), (facetIndex 17), (facetIndex 19), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87)]
theorem leaf0310_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0310 = true := by
  decide +kernel
theorem leaf0310_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0310 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0310_counts_checked
def leaf0311 : List (Fin data.count) := [(facetIndex 2), (facetIndex 16), (facetIndex 17), (facetIndex 19), (facetIndex 30), (facetIndex 32), (facetIndex 38), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87)]
theorem leaf0311_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0311 = true := by
  decide +kernel
theorem leaf0311_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0311 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0311_counts_checked
def leaf0312 : List (Fin data.count) := [(facetIndex 8), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 66), (facetIndex 69), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87)]
theorem leaf0312_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0312 = true := by
  decide +kernel
theorem leaf0312_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0312 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0312_counts_checked
def leaf0313 : List (Fin data.count) := [(facetIndex 8), (facetIndex 15), (facetIndex 16), (facetIndex 17), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 57), (facetIndex 66), (facetIndex 69), (facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 87)]
theorem leaf0313_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0313 = true := by
  decide +kernel
theorem leaf0313_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0313 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0313_counts_checked
def leaf0314 : List (Fin data.count) := [(facetIndex 3), (facetIndex 16), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 35), (facetIndex 57), (facetIndex 66), (facetIndex 69), (facetIndex 77), (facetIndex 82), (facetIndex 85), (facetIndex 87)]
theorem leaf0314_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0314 = true := by
  decide +kernel
theorem leaf0314_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0314 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0314_counts_checked
def leaf0315 : List (Fin data.count) := [(facetIndex 3), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 30), (facetIndex 32), (facetIndex 35), (facetIndex 57), (facetIndex 66), (facetIndex 69), (facetIndex 77), (facetIndex 81), (facetIndex 85), (facetIndex 87)]
theorem leaf0315_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0315 = true := by
  decide +kernel
theorem leaf0315_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0315 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0315_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 158
 (.branch 79
 (.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
 (.branch 3
 (.leaf (leaf0002))
 (.leaf (leaf0003))))
 (.branch 6
 (.branch 5
 (.leaf (leaf0004))
 (.leaf (leaf0005)))
 (.branch 7
 (.leaf (leaf0006))
 (.branch 8
 (.leaf (leaf0007))
 (.leaf (leaf0008))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (leaf0009))
 (.leaf (leaf0010)))
 (.branch 12
 (.leaf (leaf0011))
 (.branch 13
 (.leaf (leaf0012))
 (.leaf (leaf0013)))))
 (.branch 16
 (.branch 15
 (.leaf (leaf0014))
 (.leaf (leaf0015)))
 (.branch 17
 (.leaf (leaf0016))
 (.branch 18
 (.leaf (leaf0017))
 (.leaf (leaf0018)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (leaf0019))
 (.leaf (leaf0020)))
 (.branch 22
 (.leaf (leaf0021))
 (.branch 23
 (.leaf (leaf0022))
 (.leaf (leaf0023)))))
 (.branch 26
 (.branch 25
 (.leaf (leaf0024))
 (.leaf (leaf0025)))
 (.branch 27
 (.leaf (leaf0026))
 (.branch 28
 (.leaf (leaf0027))
 (.leaf (leaf0028))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (leaf0029))
 (.leaf (leaf0030)))
 (.branch 32
 (.leaf (leaf0031))
 (.branch 33
 (.leaf (leaf0032))
 (.leaf (leaf0033)))))
 (.branch 36
 (.branch 35
 (.leaf (leaf0034))
 (.leaf (leaf0035)))
 (.branch 37
 (.leaf (leaf0036))
 (.branch 38
 (.leaf (leaf0037))
 (.leaf (leaf0038))))))))
 (.branch 59
 (.branch 49
 (.branch 44
 (.branch 41
 (.branch 40
 (.leaf (leaf0039))
 (.leaf (leaf0040)))
 (.branch 42
 (.leaf (leaf0041))
 (.branch 43
 (.leaf (leaf0042))
 (.leaf (leaf0043)))))
 (.branch 46
 (.branch 45
 (.leaf (leaf0044))
 (.leaf (leaf0045)))
 (.branch 47
 (.leaf (leaf0046))
 (.branch 48
 (.leaf (leaf0047))
 (.leaf (leaf0048))))))
 (.branch 54
 (.branch 51
 (.branch 50
 (.leaf (leaf0049))
 (.leaf (leaf0050)))
 (.branch 52
 (.leaf (leaf0051))
 (.branch 53
 (.leaf (leaf0052))
 (.leaf (leaf0053)))))
 (.branch 56
 (.branch 55
 (.leaf (leaf0054))
 (.leaf (leaf0055)))
 (.branch 57
 (.leaf (leaf0056))
 (.branch 58
 (.leaf (leaf0057))
 (.leaf (leaf0058)))))))
 (.branch 69
 (.branch 64
 (.branch 61
 (.branch 60
 (.leaf (leaf0059))
 (.leaf (leaf0060)))
 (.branch 62
 (.leaf (leaf0061))
 (.branch 63
 (.leaf (leaf0062))
 (.leaf (leaf0063)))))
 (.branch 66
 (.branch 65
 (.leaf (leaf0064))
 (.leaf (leaf0065)))
 (.branch 67
 (.leaf (leaf0066))
 (.branch 68
 (.leaf (leaf0067))
 (.leaf (leaf0068))))))
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf (leaf0069))
 (.leaf (leaf0070)))
 (.branch 72
 (.leaf (leaf0071))
 (.branch 73
 (.leaf (leaf0072))
 (.leaf (leaf0073)))))
 (.branch 76
 (.branch 75
 (.leaf (leaf0074))
 (.leaf (leaf0075)))
 (.branch 77
 (.leaf (leaf0076))
 (.branch 78
 (.leaf (leaf0077))
 (.leaf (leaf0078)))))))))
 (.branch 118
 (.branch 98
 (.branch 88
 (.branch 83
 (.branch 81
 (.branch 80
 (.leaf (leaf0079))
 (.leaf (leaf0080)))
 (.branch 82
 (.leaf (leaf0081))
 (.leaf (leaf0082))))
 (.branch 85
 (.branch 84
 (.leaf (leaf0083))
 (.leaf (leaf0084)))
 (.branch 86
 (.leaf (leaf0085))
 (.branch 87
 (.leaf (leaf0086))
 (.leaf (leaf0087))))))
 (.branch 93
 (.branch 90
 (.branch 89
 (.leaf (leaf0088))
 (.leaf (leaf0089)))
 (.branch 91
 (.leaf (leaf0090))
 (.branch 92
 (.leaf (leaf0091))
 (.leaf (leaf0092)))))
 (.branch 95
 (.branch 94
 (.leaf (leaf0093))
 (.leaf (leaf0094)))
 (.branch 96
 (.leaf (leaf0095))
 (.branch 97
 (.leaf (leaf0096))
 (.leaf (leaf0097)))))))
 (.branch 108
 (.branch 103
 (.branch 100
 (.branch 99
 (.leaf (leaf0098))
 (.leaf (leaf0099)))
 (.branch 101
 (.leaf (leaf0100))
 (.branch 102
 (.leaf (leaf0101))
 (.leaf (leaf0102)))))
 (.branch 105
 (.branch 104
 (.leaf (leaf0103))
 (.leaf (leaf0104)))
 (.branch 106
 (.leaf (leaf0105))
 (.branch 107
 (.leaf (leaf0106))
 (.leaf (leaf0107))))))
 (.branch 113
 (.branch 110
 (.branch 109
 (.leaf (leaf0108))
 (.leaf (leaf0109)))
 (.branch 111
 (.leaf (leaf0110))
 (.branch 112
 (.leaf (leaf0111))
 (.leaf (leaf0112)))))
 (.branch 115
 (.branch 114
 (.leaf (leaf0113))
 (.leaf (leaf0114)))
 (.branch 116
 (.leaf (leaf0115))
 (.branch 117
 (.leaf (leaf0116))
 (.leaf (leaf0117))))))))
 (.branch 138
 (.branch 128
 (.branch 123
 (.branch 120
 (.branch 119
 (.leaf (leaf0118))
 (.leaf (leaf0119)))
 (.branch 121
 (.leaf (leaf0120))
 (.branch 122
 (.leaf (leaf0121))
 (.leaf (leaf0122)))))
 (.branch 125
 (.branch 124
 (.leaf (leaf0123))
 (.leaf (leaf0124)))
 (.branch 126
 (.leaf (leaf0125))
 (.branch 127
 (.leaf (leaf0126))
 (.leaf (leaf0127))))))
 (.branch 133
 (.branch 130
 (.branch 129
 (.leaf (leaf0128))
 (.leaf (leaf0129)))
 (.branch 131
 (.leaf (leaf0130))
 (.branch 132
 (.leaf (leaf0131))
 (.leaf (leaf0132)))))
 (.branch 135
 (.branch 134
 (.leaf (leaf0133))
 (.leaf (leaf0134)))
 (.branch 136
 (.leaf (leaf0135))
 (.branch 137
 (.leaf (leaf0136))
 (.leaf (leaf0137)))))))
 (.branch 148
 (.branch 143
 (.branch 140
 (.branch 139
 (.leaf (leaf0138))
 (.leaf (leaf0139)))
 (.branch 141
 (.leaf (leaf0140))
 (.branch 142
 (.leaf (leaf0141))
 (.leaf (leaf0142)))))
 (.branch 145
 (.branch 144
 (.leaf (leaf0143))
 (.leaf (leaf0144)))
 (.branch 146
 (.leaf (leaf0145))
 (.branch 147
 (.leaf (leaf0146))
 (.leaf (leaf0147))))))
 (.branch 153
 (.branch 150
 (.branch 149
 (.leaf (leaf0148))
 (.leaf (leaf0149)))
 (.branch 151
 (.leaf (leaf0150))
 (.branch 152
 (.leaf (leaf0151))
 (.leaf (leaf0152)))))
 (.branch 155
 (.branch 154
 (.leaf (leaf0153))
 (.leaf (leaf0154)))
 (.branch 156
 (.leaf (leaf0155))
 (.branch 157
 (.leaf (leaf0156))
 (.leaf (leaf0157))))))))))
 (.branch 237
 (.branch 197
 (.branch 177
 (.branch 167
 (.branch 162
 (.branch 160
 (.branch 159
 (.leaf (leaf0158))
 (.leaf (leaf0159)))
 (.branch 161
 (.leaf (leaf0160))
 (.leaf (leaf0161))))
 (.branch 164
 (.branch 163
 (.leaf (leaf0162))
 (.leaf (leaf0163)))
 (.branch 165
 (.leaf (leaf0164))
 (.branch 166
 (.leaf (leaf0165))
 (.leaf (leaf0166))))))
 (.branch 172
 (.branch 169
 (.branch 168
 (.leaf (leaf0167))
 (.leaf (leaf0168)))
 (.branch 170
 (.leaf (leaf0169))
 (.branch 171
 (.leaf (leaf0170))
 (.leaf (leaf0171)))))
 (.branch 174
 (.branch 173
 (.leaf (leaf0172))
 (.leaf (leaf0173)))
 (.branch 175
 (.leaf (leaf0174))
 (.branch 176
 (.leaf (leaf0175))
 (.leaf (leaf0176)))))))
 (.branch 187
 (.branch 182
 (.branch 179
 (.branch 178
 (.leaf (leaf0177))
 (.leaf (leaf0178)))
 (.branch 180
 (.leaf (leaf0179))
 (.branch 181
 (.leaf (leaf0180))
 (.leaf (leaf0181)))))
 (.branch 184
 (.branch 183
 (.leaf (leaf0182))
 (.leaf (leaf0183)))
 (.branch 185
 (.leaf (leaf0184))
 (.branch 186
 (.leaf (leaf0185))
 (.leaf (leaf0186))))))
 (.branch 192
 (.branch 189
 (.branch 188
 (.leaf (leaf0187))
 (.leaf (leaf0188)))
 (.branch 190
 (.leaf (leaf0189))
 (.branch 191
 (.leaf (leaf0190))
 (.leaf (leaf0191)))))
 (.branch 194
 (.branch 193
 (.leaf (leaf0192))
 (.leaf (leaf0193)))
 (.branch 195
 (.leaf (leaf0194))
 (.branch 196
 (.leaf (leaf0195))
 (.leaf (leaf0196))))))))
 (.branch 217
 (.branch 207
 (.branch 202
 (.branch 199
 (.branch 198
 (.leaf (leaf0197))
 (.leaf (leaf0198)))
 (.branch 200
 (.leaf (leaf0199))
 (.branch 201
 (.leaf (leaf0200))
 (.leaf (leaf0201)))))
 (.branch 204
 (.branch 203
 (.leaf (leaf0202))
 (.leaf (leaf0203)))
 (.branch 205
 (.leaf (leaf0204))
 (.branch 206
 (.leaf (leaf0205))
 (.leaf (leaf0206))))))
 (.branch 212
 (.branch 209
 (.branch 208
 (.leaf (leaf0207))
 (.leaf (leaf0208)))
 (.branch 210
 (.leaf (leaf0209))
 (.branch 211
 (.leaf (leaf0210))
 (.leaf (leaf0211)))))
 (.branch 214
 (.branch 213
 (.leaf (leaf0212))
 (.leaf (leaf0213)))
 (.branch 215
 (.leaf (leaf0214))
 (.branch 216
 (.leaf (leaf0215))
 (.leaf (leaf0216)))))))
 (.branch 227
 (.branch 222
 (.branch 219
 (.branch 218
 (.leaf (leaf0217))
 (.leaf (leaf0218)))
 (.branch 220
 (.leaf (leaf0219))
 (.branch 221
 (.leaf (leaf0220))
 (.leaf (leaf0221)))))
 (.branch 224
 (.branch 223
 (.leaf (leaf0222))
 (.leaf (leaf0223)))
 (.branch 225
 (.leaf (leaf0224))
 (.branch 226
 (.leaf (leaf0225))
 (.leaf (leaf0226))))))
 (.branch 232
 (.branch 229
 (.branch 228
 (.leaf (leaf0227))
 (.leaf (leaf0228)))
 (.branch 230
 (.leaf (leaf0229))
 (.branch 231
 (.leaf (leaf0230))
 (.leaf (leaf0231)))))
 (.branch 234
 (.branch 233
 (.leaf (leaf0232))
 (.leaf (leaf0233)))
 (.branch 235
 (.leaf (leaf0234))
 (.branch 236
 (.leaf (leaf0235))
 (.leaf (leaf0236)))))))))
 (.branch 276
 (.branch 256
 (.branch 246
 (.branch 241
 (.branch 239
 (.branch 238
 (.leaf (leaf0237))
 (.leaf (leaf0238)))
 (.branch 240
 (.leaf (leaf0239))
 (.leaf (leaf0240))))
 (.branch 243
 (.branch 242
 (.leaf (leaf0241))
 (.leaf (leaf0242)))
 (.branch 244
 (.leaf (leaf0243))
 (.branch 245
 (.leaf (leaf0244))
 (.leaf (leaf0245))))))
 (.branch 251
 (.branch 248
 (.branch 247
 (.leaf (leaf0246))
 (.leaf (leaf0247)))
 (.branch 249
 (.leaf (leaf0248))
 (.branch 250
 (.leaf (leaf0249))
 (.leaf (leaf0250)))))
 (.branch 253
 (.branch 252
 (.leaf (leaf0251))
 (.leaf (leaf0252)))
 (.branch 254
 (.leaf (leaf0253))
 (.branch 255
 (.leaf (leaf0254))
 (.leaf (leaf0255)))))))
 (.branch 266
 (.branch 261
 (.branch 258
 (.branch 257
 (.leaf (leaf0256))
 (.leaf (leaf0257)))
 (.branch 259
 (.leaf (leaf0258))
 (.branch 260
 (.leaf (leaf0259))
 (.leaf (leaf0260)))))
 (.branch 263
 (.branch 262
 (.leaf (leaf0261))
 (.leaf (leaf0262)))
 (.branch 264
 (.leaf (leaf0263))
 (.branch 265
 (.leaf (leaf0264))
 (.leaf (leaf0265))))))
 (.branch 271
 (.branch 268
 (.branch 267
 (.leaf (leaf0266))
 (.leaf (leaf0267)))
 (.branch 269
 (.leaf (leaf0268))
 (.branch 270
 (.leaf (leaf0269))
 (.leaf (leaf0270)))))
 (.branch 273
 (.branch 272
 (.leaf (leaf0271))
 (.leaf (leaf0272)))
 (.branch 274
 (.leaf (leaf0273))
 (.branch 275
 (.leaf (leaf0274))
 (.leaf (leaf0275))))))))
 (.branch 296
 (.branch 286
 (.branch 281
 (.branch 278
 (.branch 277
 (.leaf (leaf0276))
 (.leaf (leaf0277)))
 (.branch 279
 (.leaf (leaf0278))
 (.branch 280
 (.leaf (leaf0279))
 (.leaf (leaf0280)))))
 (.branch 283
 (.branch 282
 (.leaf (leaf0281))
 (.leaf (leaf0282)))
 (.branch 284
 (.leaf (leaf0283))
 (.branch 285
 (.leaf (leaf0284))
 (.leaf (leaf0285))))))
 (.branch 291
 (.branch 288
 (.branch 287
 (.leaf (leaf0286))
 (.leaf (leaf0287)))
 (.branch 289
 (.leaf (leaf0288))
 (.branch 290
 (.leaf (leaf0289))
 (.leaf (leaf0290)))))
 (.branch 293
 (.branch 292
 (.leaf (leaf0291))
 (.leaf (leaf0292)))
 (.branch 294
 (.leaf (leaf0293))
 (.branch 295
 (.leaf (leaf0294))
 (.leaf (leaf0295)))))))
 (.branch 306
 (.branch 301
 (.branch 298
 (.branch 297
 (.leaf (leaf0296))
 (.leaf (leaf0297)))
 (.branch 299
 (.leaf (leaf0298))
 (.branch 300
 (.leaf (leaf0299))
 (.leaf (leaf0300)))))
 (.branch 303
 (.branch 302
 (.leaf (leaf0301))
 (.leaf (leaf0302)))
 (.branch 304
 (.leaf (leaf0303))
 (.branch 305
 (.leaf (leaf0304))
 (.leaf (leaf0305))))))
 (.branch 311
 (.branch 308
 (.branch 307
 (.leaf (leaf0306))
 (.leaf (leaf0307)))
 (.branch 309
 (.leaf (leaf0308))
 (.branch 310
 (.leaf (leaf0309))
 (.leaf (leaf0310)))))
 (.branch 313
 (.branch 312
 (.leaf (leaf0311))
 (.leaf (leaf0312)))
 (.branch 314
 (.leaf (leaf0313))
 (.branch 315
 (.leaf (leaf0314))
 (.leaf (leaf0315)))))))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":1},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":3},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0050\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0050\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0059\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0059\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0066\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0064\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0060\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0060\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0060\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0069\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0069\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0073\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0073\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0070\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0070\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007" 221

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007" "{\"ridges\":[[0,7],[0,70],[1,7],[1,259],[1,261],[1,262],[2,11],[2,131],[3,11],[4,131],[5,21],[5,84],[6,517],[6,532],[7,261],[7,517],[7,769],[7,772],[8,25],[8,145],[9,536],[10,265],[10,776],[11,81],[11,193],[12,38],[13,38],[13,290],[14,42],[15,42],[15,266],[15,290],[15,296],[16,224],[17,52],[17,100],[18,168],[20,11],[20,30],[21,11],[21,45],[22,11],[22,261],[23,7],[23,11],[23,526],[24,51],[25,7],[25,67],[25,81],[25,84],[26,150],[27,7],[27,38],[27,67],[27,69],[27,98],[27,100],[28,165],[29,7],[29,38],[29,290],[29,292],[30,7],[30,69],[30,70],[30,131],[30,193],[30,194],[31,67],[31,69],[31,70],[31,259],[31,261],[31,262],[32,7],[32,259],[32,262],[32,517],[32,769],[32,772],[33,51],[34,90],[35,11],[35,131],[35,138],[35,145],[35,152],[36,105],[37,11],[37,42],[37,162],[37,168],[38,11],[38,42],[38,259],[38,290],[39,11],[39,67],[39,137],[39,138],[39,193],[39,194],[40,131],[40,137],[40,138],[40,259],[40,265],[40,266],[41,11],[41,259],[41,266],[41,521],[41,769],[41,776],[42,51],[43,51],[44,67],[44,81],[44,131],[44,194],[45,67],[45,98],[45,131],[45,162],[45,193],[45,224],[46,353],[47,417],[48,45],[48,52],[50,21],[50,25],[50,517],[50,521],[50,532],[50,536],[51,45],[52,261],[52,265],[52,517],[52,521],[52,772],[52,776],[53,21],[53,52],[53,69],[53,81],[53,100],[53,112],[54,165],[55,305],[56,21],[56,69],[56,84],[56,193],[56,208],[57,69],[57,81],[57,84],[57,517],[57,529],[57,532],[58,21],[58,261],[58,529],[58,532],[58,769],[58,772],[59,165],[60,353],[61,105],[62,25],[62,145],[62,168],[62,176],[63,305],[64,25],[64,81],[64,137],[64,152],[64,193],[64,208],[65,137],[65,145],[65,152],[65,521],[65,529],[65,536],[66,25],[66,265],[66,529],[66,536],[66,769],[66,776],[67,105],[68,417],[69,112],[69,145],[69,176],[69,193],[69,224],[70,30],[70,52],[71,38],[71,42],[71,262],[71,266],[71,292],[71,296],[72,262],[72,266],[72,526],[73,38],[73,52],[73,70],[73,84],[73,98],[73,112],[74,150],[75,150],[76,38],[76,70],[76,100],[76,194],[76,224],[77,70],[77,98],[77,100],[77,262],[77,290],[77,292],[78,90],[79,42],[79,56],[79,138],[79,152],[79,162],[79,176],[80,90],[81,42],[81,98],[81,138],[81,168],[81,194],[81,224],[82,138],[82,162],[82,168],[82,266],[82,290],[82,296],[83,98],[83,112],[83,162],[83,176],[83,208],[85,52],[85,56],[85,532],[85,556],[86,284],[86,776],[87,292],[87,296],[87,556],[87,772],[88,52],[88,84],[88,100],[88,176],[88,208],[88,224],[89,52],[89,532],[89,772],[89,816],[90,112],[90,152],[90,168],[90,208],[90,224],[91,56],[91,536],[91,776],[91,816]],\"owners\":[[0,7,[1,20,21,22,23,24,26,28,29,32],[25,27,30]],[1,7,[0,20,21,23,24,25,26,27,28,30],[22,29,32]],[25,7,[1,21,22,23,28,29,32],[0,20,24,26,27,30]],[27,7,[1,20,22,23,26,32],[0,21,24,25,28,29,30]],[29,7,[0,20,23,25,26,30],[1,21,22,24,27,28,32]],[30,7,[1,20,21,22,23,24,29,32],[0,25,26,27,28]],[32,7,[0,20,21,24,25,26,27,28,30],[1,22,23,29]],[25,67,[4,36,39,45,46],[0,27,31,34,42,44]],[27,67,[4,34,39,44],[0,25,31,36,42,45,46]],[31,67,[4,34,36,39,42,44,45],[0,25,27,46]],[39,67,[0,25,27,31,42,46],[4,34,36,44,45]],[44,67,[0,27,31,36,46],[4,25,34,39,42,45]],[45,67,[0,25,31,34],[4,27,36,39,42,44,46]],[27,69,[5,56,57],[0,30,31,53,59,60]],[30,69,[5,53,57,60],[0,27,31,56,59]],[31,69,[5,53,56,57,59],[0,27,30,60]],[53,69,[0,30,31],[5,27,56,57,59,60]],[56,69,[0,27,31,60],[5,30,53,57,59]],[57,69,[0,27,30,31,59,60],[5,53,56]],[0,70,[12,73,75,76,77],[25,30,31]],[30,70,[12,73,77],[0,25,31,75,76]],[31,70,[12,73,75,76],[0,25,30,77]],[73,70,[0,30,31],[12,25,75,76,77]],[76,70,[0,25,31],[12,30,73,75,77]],[77,70,[0,25,30,75],[12,31,73,76]],[1,259,[3,38,40,41,46,47],[29,31,32]],[31,259,[3,38,40,41,47],[1,29,32,46]],[32,259,[3,38,40,46,47],[1,29,31,41]],[38,259,[1,31,32],[3,29,40,41,46,47]],[40,259,[1,29,31,32,46],[3,38,41,47]],[41,259,[1,29,31,46,47],[3,32,38,40]],[1,261,[7,49,51,52,55,58,60],[22,29,31]],[7,261,[1,22,29,31,49,51,55,60],[52,58]],[22,261,[7,55,58,60],[1,29,31,49,51,52]],[31,261,[7,49,51,52,55,58],[1,22,29,60]],[52,261,[1,29,31,55,60],[7,22,49,51,58]],[58,261,[1,22,29,31,51,60],[7,49,52,55]],[1,262,[13,71,72,77],[22,31,32]],[31,262,[13,71,72],[1,22,32,77]],[32,262,[13,71,77],[1,22,31,72]],[71,262,[1,31,32],[13,22,72,77]],[77,262,[1,22,32,72],[13,31,71]],[3,11,[2,20,21,23,33,34,35,36,37,39],[22,38,41]],[22,11,[2,33,34,35,36,37,39],[3,20,21,23,38,41]],[35,11,[3,21,22,23,36,38,41],[2,20,33,34,37,39]],[37,11,[3,20,22,23,34,41],[2,21,33,35,36,38,39]],[38,11,[2,20,23,34,35,39],[3,21,22,33,36,37,41]],[39,11,[3,20,21,22,23,33,38,41],[2,34,35,36,37]],[41,11,[2,20,21,33,34,35,36,37,39],[3,22,23,38]],[2,131,[4,26,28,30,43,44,45,47],[35,37,40]],[4,131,[2,26,28,35,37,40,43,47],[30,44,45]],[30,131,[2,35,37,40,43,47],[4,26,28,44,45]],[35,131,[4,28,30,45,47],[2,26,37,40,43,44]],[40,131,[4,26,28,30,43,44,45],[2,35,37,47]],[44,131,[2,28,37,40,47],[4,26,30,35,43,45]],[45,131,[2,26,35,40],[4,28,30,37,43,44,47]],[39,137,[8,62,65,68],[2,37,40,64,67]],[40,137,[8,62,64,65,67],[2,37,39,68]],[64,137,[2,37,40,68],[8,39,62,65,67]],[65,137,[2,37,39,40,67,68],[8,62,64]],[35,138,[14,81,82],[2,39,40,79,80]],[39,138,[14,79,82],[2,35,40,80,81]],[40,138,[14,79,80,81],[2,35,39,82]],[79,138,[2,39,40],[14,35,80,81,82]],[81,138,[2,35,40],[14,39,79,80,82]],[82,138,[2,35,39,80],[14,40,79,81]],[10,265,[3,22,38,40,49,51,63,68],[52,66]],[40,265,[10,49,51,52,63,66],[3,22,38,68]],[52,265,[3,38,40,63,68],[10,22,49,51,66]],[66,265,[3,22,38,40,51,68],[10,49,52,63]],[40,266,[15,71,72],[3,22,41,82]],[41,266,[15,71,82],[3,22,40,72]],[71,266,[3,40,41],[15,22,72,82]],[82,266,[3,22,41,72],[15,40,71]],[11,193,[4,30,39,45,59,67],[56,64,69]],[30,193,[11,64,67,69],[4,39,45,56,59]],[39,193,[11,56,59,69],[4,30,45,64,67]],[45,193,[11,56,64],[4,30,39,59,67,69]],[56,193,[4,39,45,67],[11,30,59,64,69]],[64,193,[4,30,45,59],[11,39,56,67,69]],[69,193,[4,30,39],[11,45,56,59,64,67]],[30,194,[16,80,81,83],[4,39,44,75,76]],[39,194,[16,75,76,83],[4,30,44,80,81]],[44,194,[16,76,81],[4,30,39,75,80,83]],[76,194,[4,39,44,80],[16,30,75,81,83]],[81,194,[4,30,44,75],[16,39,76,80,83]],[5,21,[6,20,24,26,48,49,50,54,55,58],[25,53,56]],[50,21,[5,24,25,26,53,54,55,56],[6,20,48,49,58]],[53,21,[6,20,26,49,50,58],[5,24,25,48,54,55,56]],[56,21,[6,20,24,48,49,50,55,58],[5,25,26,53,54]],[58,21,[5,20,24,25,26,48,53,54,56],[6,49,50,55]],[11,81,[5,25,34,42,53,57,61],[44,64,69]],[25,81,[11,61,64,69],[5,34,42,44,53,57]],[44,81,[5,53,57,61],[11,25,34,42,64,69]],[53,81,[11,34,44,64],[5,25,42,57,61,69]],[57,81,[11,34,42,44,61,64,69],[5,25,53]],[64,81,[5,25,42,53,57],[11,34,44,61,69]],[5,84,[17,73,75,88],[25,56,57]],[25,84,[17,88],[5,56,57,73,75]],[56,84,[17,73],[5,25,57,75,88]],[57,84,[17,73,75,88],[5,25,56]],[73,84,[5,56,57],[17,25,75,88]],[88,84,[5,25,57],[17,56,73,75]],[6,517,[7,23,32,52],[50,57]],[7,517,[6,23,50,57],[32,52]],[32,517,[6,50,57],[7,23,52]],[50,517,[7,32],[6,23,52,57]],[52,517,[6,57],[7,23,32,50]],[57,517,[7,23,32,52],[6,50]],[57,529,[9,65,66],[6,58]],[58,529,[9,65],[6,57,66]],[65,529,[6,57,58],[9,66]],[66,529,[6,57],[9,58,65]],[6,532,[85,86,89],[50,57,58]],[50,532,[89],[6,57,58,85,86]],[57,532,[85,86,89],[6,50,58]],[58,532,[85],[6,50,57,86,89]],[85,532,[6,57,58],[50,86,89]],[89,532,[6,50,57],[58,85,86]],[7,769,[10,41,66],[32,58]],[32,769,[10,66],[7,41,58]],[41,769,[7,58],[10,32,66]],[58,769,[10,41],[7,32,66]],[66,769,[7,32],[10,41,58]],[7,772,[72,86,87,89],[32,52,58]],[32,772,[86,87,89],[7,52,58,72]],[52,772,[89],[7,32,58,72,86,87]],[58,772,[72,87],[7,32,52,86,89]],[87,772,[7,32,58],[52,72,86,89]],[89,772,[7,32,52,72],[58,86,87]],[8,25,[9,20,33,34,48,49,50,61,63,66],[35,62,64]],[50,25,[8,33,34,35,61,62,63,64],[9,20,48,49,66]],[62,25,[9,20,34,49,50,66],[8,33,35,48,61,63,64]],[64,25,[9,20,33,48,49,50,63,66],[8,34,35,61,62]],[66,25,[8,20,33,34,35,48,61,62,64],[9,49,50,63]],[8,145,[11,26,43,44,54,56,69],[35,62,65]],[35,145,[11,54,56,69],[8,26,43,44,62,65]],[62,145,[11,26,44,56],[8,35,43,54,65,69]],[65,145,[11,26,43,44,54,56,69],[8,35,62]],[69,145,[8,26,35,65],[11,43,44,54,56,62]],[35,152,[18,90],[8,64,65,79,80]],[64,152,[18,79],[8,35,65,80,90]],[65,152,[18,79,80,90],[8,35,64]],[79,152,[8,64,65],[18,35,80,90]],[90,152,[8,35,65],[18,64,79,80]],[41,521,[9,50,65],[10,23,52]],[50,521,[10,41],[9,23,52,65]],[52,521,[9,65],[10,23,41,50]],[65,521,[10,23,41,52],[9,50]],[9,536,[85,86,91],[50,65,66]],[50,536,[91],[9,65,66,85,86]],[65,536,[85,86,91],[9,50,66]],[66,536,[85],[9,50,65,86,91]],[91,536,[9,50,65],[66,85,86]],[10,776,[72,86,87,91],[41,52,66]],[41,776,[86,87,91],[10,52,66,72]],[52,776,[91],[10,41,66,72,86,87]],[66,776,[72,87],[10,41,52,86,91]],[86,776,[10,41],[52,66,72,87,91]],[91,776,[10,41,52,72],[66,86,87]],[56,208,[19,80,83,90],[11,44,64,75,88]],[64,208,[19,75,83,88],[11,44,56,80,90]],[83,208,[11,56,64],[19,44,75,80,88,90]],[88,208,[11,44,64,80],[19,56,75,83,90]],[90,208,[11,44,56,75],[19,64,80,83,88]],[12,38,[13,21,24,28,29,70,71,74],[27,73,76]],[13,38,[12,21,24,27,28,70,73,74,76],[29,71]],[27,38,[13,70,71,74],[12,21,24,28,29,73,76]],[29,38,[12,70,73,74,76],[13,21,24,27,28,71]],[71,38,[12,24,27,28,73,74,76],[13,21,29,70]],[73,38,[13,21,28,29,71],[12,24,27,70,74,76]],[76,38,[13,21,24,29,70,71],[12,27,28,73,74]],[27,98,[16,78,81,83],[12,36,42,45,46,73,77]],[45,98,[12,73,77,78],[16,27,36,42,46,81,83]],[73,98,[16,36,45,46,81],[12,27,42,77,78,83]],[77,98,[16,36,42,45,78,81,83],[12,27,46,73]],[81,98,[12,27,42,46,73,77],[16,36,45,78,83]],[83,98,[12,27,36,46,77],[16,42,45,73,78,81]],[17,100,[12,27,59,60,76,77],[53,88]],[27,100,[17,88],[12,53,59,60,76,77]],[53,100,[12,76,77],[17,27,59,60,88]],[76,100,[17,53,60],[12,27,59,77,88]],[77,100,[17,53,59,88],[12,27,60,76]],[88,100,[12,27,60,77],[17,53,59,76]],[13,290,[15,38,46,47,82],[29,77]],[15,290,[13,29,46,47,77],[38,82]],[29,290,[15,82],[13,38,46,47,77]],[38,290,[13,77],[15,29,46,47,82]],[77,290,[15,38,47,82],[13,29,46]],[82,290,[13,29,46,77],[15,38,47]],[29,292,[84,87,89],[13,51,55,60,71,77]],[71,292,[55,60,89],[13,29,51,77,84,87]],[77,292,[51,55,84,87,89],[13,29,60,71]],[87,292,[13,29,55,60,77],[51,71,84,89]],[14,42,[15,21,33,36,38,70,71,78],[37,79,81]],[15,42,[14,21,33,36,37,70,78,79,81],[38,71]],[37,42,[15,70,71,78],[14,21,33,36,38,79,81]],[38,42,[14,70,78,79,81],[15,21,33,36,37,71]],[71,42,[14,33,36,37,78,79,81],[15,21,38,70]],[79,42,[15,21,36,38,71],[14,33,37,70,78,81]],[81,42,[15,21,33,38,70,71],[14,36,37,78,79]],[37,162,[16,74,76,83],[14,28,43,45,47,79,82]],[45,162,[14,74,79,82],[16,28,37,43,47,76,83]],[79,162,[16,28,45,47,76],[14,37,43,74,82,83]],[82,162,[16,28,43,45,74,76,83],[14,37,47,79]],[83,162,[14,28,37,47,82],[16,43,45,74,76,79]],[18,168,[14,37,67,68,81,82],[62,90]],[37,168,[18,90],[14,62,67,68,81,82]],[62,168,[14,81,82],[18,37,67,68,90]],[81,168,[18,62,68],[14,37,67,82,90]],[82,168,[18,62,67,90],[14,37,68,81]],[90,168,[14,37,68,82],[18,62,67,81]],[15,296,[51,63,68,84,87,91],[38,71,82]],[71,296,[63,68,91],[15,38,51,82,84,87]],[82,296,[51,63,84,87,91],[15,38,68,71]],[87,296,[15,38,63,68,82],[51,71,84,91]],[16,224,[19,59,67,69,88,90],[45,76,81]],[45,224,[19,88,90],[16,59,67,69,76,81]],[69,224,[16,76,81],[19,45,59,67,88,90]],[76,224,[19,67,69,90],[16,45,59,81,88]],[81,224,[19,59,69,88],[16,45,67,76,90]],[88,224,[16,45,67,81],[19,59,69,76,90]],[90,224,[16,45,59,76],[19,67,69,81,88]],[17,52,[24,48,54,55,70,74,84,85,89],[53,73,88]],[53,52,[70,74,84,85,89],[17,24,48,54,55,73,88]],[73,52,[48,54,55,84,85,89],[17,24,53,70,74,88]],[85,52,[17,24,53,54,55,73,74,88],[48,70,84,89]],[88,52,[24,48,55,70,84,85,89],[17,53,54,73,74]],[89,52,[17,24,48,53,54,70,73,74,88],[55,84,85]],[53,112,[19,78,83,90],[17,42,61,69,73]],[69,112,[17,73,78],[19,42,53,61,83,90]],[73,112,[19,61,69,90],[17,42,53,78,83]],[83,112,[17,53,61],[19,42,69,73,78,90]],[90,112,[17,42,53,73],[19,61,69,78,83]],[79,56,[48,61,63,84,85,91],[18,33,62,70,78,90]],[85,56,[18,33,61,62,63,78,79,90],[48,70,84,91]],[91,56,[18,33,48,61,62,70,78,79,90],[63,84,85]],[62,176,[19,74,83,88],[18,43,54,69,79]],[69,176,[18,74,79],[19,43,54,62,83,88]],[79,176,[19,54,69,88],[18,43,62,74,83]],[83,176,[18,54,62],[19,43,69,74,79,88]],[88,176,[18,43,62,79],[19,54,69,74,83]],[20,30,[70],[]],[70,30,[20],[]],[21,45,[48,51],[]],[48,45,[21,51],[]],[51,45,[21,48],[]],[23,526,[72],[]],[72,526,[23],[]],[24,51,[33,42,43],[]],[33,51,[24,42,43],[]],[42,51,[24,33,43],[]],[43,51,[24,33,42],[]],[26,150,[74,75],[]],[74,150,[26,75],[]],[75,150,[26,74],[]],[28,165,[54,59],[]],[54,165,[28,59],[]],[59,165,[28,54],[]],[34,90,[78,80],[]],[78,90,[34,80],[]],[80,90,[34,78],[]],[36,105,[61,67],[]],[61,105,[36,67],[]],[67,105,[36,61],[]],[46,353,[60],[]],[60,353,[46],[]],[47,417,[68],[]],[68,417,[47],[]],[86,284,[49,84],[]],[55,305,[63],[]],[63,305,[55],[]],[85,556,[87],[]],[87,556,[85],[]],[89,816,[91],[]],[91,816,[89],[]]],\"edges\":[[8,[6,7,9,10,23,32,41,50,52,57,58,65,66]],[23,[6,7,23,32,50,52,57,58,72,85,86,87,89]],[34,[6,9,50,57,58,65,66,85,86,89,91]],[44,[7,10,32,41,52,58,66,72,86,87,89,91]]],\"groupings\":[1,2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-2],[-26,-1],[-28,-1],[-28,-26],[-30,-2],[-30,-23],[-30,-28],[-31,-1],[-31,-26],[-31,-28],[-32,-2],[-32,-21],[-32,-22],[-32,-23],[-32,-24],[-32,-26],[-32,-28],[-32,-30],[-32,-31],[-33,-2],[-33,-24],[-33,-30],[-33,-32],[-36,-21],[-36,-26],[-38,-3],[-38,-15],[-38,-22],[-38,-28],[-38,-30],[-38,-36],[-39,-23],[-39,-28],[-39,-30],[-39,-38],[-40,-3],[-40,-5],[-40,-31],[-40,-36],[-40,-38],[-41,-3],[-41,-21],[-41,-22],[-41,-23],[-41,-24],[-41,-36],[-41,-38],[-41,-39],[-41,-40],[-42,-4],[-42,-23],[-42,-24],[-42,-33],[-42,-39],[-42,-41],[-45,-21],[-45,-26],[-45,-31],[-45,-36],[-45,-40],[-46,-22],[-46,-28],[-46,-30],[-46,-31],[-46,-38],[-46,-39],[-46,-40],[-46,-45],[-49,-30],[-50,-42],[-51,-21],[-51,-22],[-51,-23],[-51,-24],[-51,-49],[-51,-50],[-53,-21],[-53,-22],[-53,-23],[-53,-24],[-53,-33],[-53,-42],[-53,-51],[-54,-18],[-54,-22],[-54,-26],[-54,-28],[-54,-30],[-54,-38],[-54,-39],[-54,-46],[-57,-6],[-57,-26],[-57,-31],[-57,-45],[-57,-54],[-58,-21],[-58,-26],[-58,-49],[-58,-50],[-58,-51],[-58,-54],[-58,-57],[-59,-7],[-59,-8],[-59,-24],[-59,-33],[-59,-50],[-59,-53],[-59,-58],[-63,-9],[-63,-22],[-63,-28],[-63,-30],[-63,-36],[-63,-38],[-63,-39],[-63,-46],[-63,-49],[-63,-54],[-65,-12],[-65,-36],[-65,-40],[-65,-45],[-65,-57],[-65,-63],[-66,-21],[-66,-36],[-66,-49],[-66,-50],[-66,-51],[-66,-63],[-66,-65],[-67,-24],[-67,-42],[-67,-51],[-67,-53],[-67,-59],[-67,-66],[-70,-28],[-70,-30],[-70,-38],[-70,-39],[-70,-45],[-70,-46],[-70,-54],[-70,-57],[-70,-63],[-70,-65],[-71,-45],[-71,-51],[-71,-53],[-72,-14],[-72,-16],[-72,-21],[-72,-23],[-72,-30],[-72,-39],[-72,-50],[-72,-51],[-72,-53],[-73,-30],[-73,-33],[-73,-39],[-73,-42],[-73,-51],[-73,-53],[-73,-72],[-74,-26],[-74,-28],[-74,-36],[-74,-45],[-74,-54],[-77,-13],[-77,-28],[-77,-31],[-77,-46],[-77,-57],[-77,-74],[-78,-22],[-78,-28],[-78,-30],[-78,-32],[-78,-71],[-78,-72],[-78,-74],[-78,-77],[-80,-15],[-80,-19],[-80,-26],[-80,-36],[-80,-38],[-80,-45],[-80,-63],[-80,-74],[-82,-38],[-82,-40],[-82,-46],[-82,-65],[-82,-77],[-82,-80],[-83,-22],[-83,-38],[-83,-39],[-83,-41],[-83,-71],[-83,-72],[-83,-80],[-83,-82],[-84,-17],[-84,-26],[-84,-36],[-84,-45],[-84,-46],[-84,-70],[-84,-74],[-84,-77],[-84,-80],[-84,-82],[-85,-59],[-85,-67],[-86,-22],[-86,-23],[-86,-24],[-86,-50],[-86,-51],[-86,-71],[-86,-72],[-87,-51],[-87,-59],[-87,-72],[-89,-18],[-89,-31],[-89,-54],[-89,-57],[-89,-70],[-89,-74],[-89,-77],[-89,-84],[-90,-59],[-90,-67],[-91,-40],[-91,-63],[-91,-65],[-91,-70],[-91,-80],[-91,-82],[-91,-84],[-91,-89],[-92,-67],[-1,2,21,22,23,24,25,27,29,30,33],[-2,1,21,22,24,25,26,27,28,29,31],[-26,2,22,23,24,29,30,33],[-28,2,21,23,24,27,33],[-30,1,21,24,26,27,31],[-31,2,21,22,23,24,25,30,33],[-33,1,21,22,25,26,27,28,29,31],[-1,-2,-24],[-2,-24,-26],[-2,-24,-31],[-26,5,37,40,46,47],[-28,5,35,40,45],[-32,5,35,37,40,43,45,46],[-40,1,26,28,32,43,47],[-45,1,28,32,37,47],[-46,1,26,32,35],[-28,6,57,58],[-31,6,54,58,61],[-32,6,54,57,58,60],[-54,1,31,32],[-57,1,28,32,61],[-58,1,28,31,32,60,61],[-1,13,74,76,77,78],[-31,13,74,78],[-32,13,74,76,77],[-74,1,31,32],[-77,1,26,32],[-78,1,26,31,76],[-2,4,39,41,42,47,48],[-32,4,39,41,42,48],[-33,4,39,41,47,48],[-39,2,32,33],[-41,2,30,32,33,47],[-42,2,30,32,47,48],[-2,8,50,52,53,56,59,61],[-8,2,23,30,32,50,52,56,61],[-23,8,56,59,61],[-32,8,50,52,53,56,59],[-53,2,30,32,56,61],[-59,2,23,30,32,52,61],[-2,14,72,73,78],[-32,14,72,73],[-33,14,72,78],[-72,2,32,33],[-78,2,23,33,73],[-2,-73,-78],[-4,3,21,22,24,34,35,36,37,38,40],[-23,3,34,35,36,37,38,40],[-36,4,22,23,24,37,39,42],[-38,4,21,23,24,35,42],[-39,3,21,24,35,36,40],[-40,4,21,22,23,24,34,39,42],[-42,3,21,22,34,35,36,37,38,40],[-3,-4,-24],[-21,-40,-42],[-22,-36,-42],[-22,-40,-42],[-3,5,27,29,31,44,45,46,48],[-5,3,27,29,36,38,41,44,48],[-31,3,36,38,41,44,48],[-36,5,29,31,46,48],[-41,5,27,29,31,44,45,46],[-45,3,29,38,41,48],[-46,3,27,36,41],[-40,9,63,66,69],[-41,9,63,65,66,68],[-65,3,38,41,69],[-66,3,38,40,41,68,69],[-36,15,82,83],[-40,15,80,83],[-41,15,80,81,82],[-80,3,40,41],[-82,3,36,41],[-83,3,36,40,81],[-11,4,23,39,41,50,52,64,69],[-41,11,50,52,53,64,67],[-53,4,39,41,64,69],[-67,4,23,39,41,52,69],[-41,16,72,73],[-42,16,72,83],[-72,4,41,42],[-83,4,23,42,73],[-16,-41,-73],[-12,5,31,40,46,60,68],[-31,12,65,68,70],[-40,12,57,60,70],[-46,12,57,65],[-57,5,40,46,68],[-65,5,31,46,60],[-70,5,31,40],[-31,17,81,82,84],[-40,17,76,77,84],[-45,17,77,82],[-77,5,40,45,81],[-82,5,31,45,76],[-6,7,21,25,27,49,50,51,55,56,59],[-51,6,25,26,27,54,55,56,57],[-54,7,21,27,50,51,59],[-57,7,21,25,49,50,51,56,59],[-59,6,21,25,26,27,49,54,55,57],[-12,6,26,35,43,54,58,62],[-26,12,62,65,70],[-45,6,54,58,62],[-54,12,35,45,65],[-58,12,35,43,45,62,65,70],[-65,6,26,43,54,58],[-6,18,74,76,89],[-26,18,89],[-57,18,74],[-58,18,74,76,89],[-74,6,57,58],[-89,6,26,58],[-7,8,24,33,53],[-8,7,24,51,58],[-33,7,51,58],[-51,8,33],[-53,7,58],[-58,8,24,33,53],[-58,10,66,67],[-59,10,66],[-66,7,58,59],[-67,7,58],[-7,86,87,90],[-51,90],[-58,86,87,90],[-59,86],[-86,7,58,59],[-90,7,51,58],[-8,11,42,67],[-33,11,67],[-42,8,59],[-59,11,42],[-67,8,33],[-8,73,87,88,90],[-33,87,88,90],[-53,90],[-59,73,88],[-88,8,33,59],[-90,8,33,53,73],[-9,10,21,34,35,49,50,51,62,64,67],[-51,9,34,35,36,62,63,64,65],[-63,10,21,35,50,51,67],[-65,10,21,34,49,50,51,64,67],[-67,9,21,34,35,36,49,62,63,65],[-9,12,27,44,45,55,57,70],[-36,12,55,57,70],[-63,12,27,45,57],[-66,12,27,44,45,55,57,70],[-70,9,27,36,66],[-36,19,91],[-65,19,80],[-66,19,80,81,91],[-80,9,65,66],[-91,9,36,66],[-42,10,51,66],[-51,11,42],[-53,10,66],[-66,11,24,42,53],[-10,86,87,92],[-51,92],[-66,86,87,92],[-67,86],[-92,10,51,66],[-11,73,87,88,92],[-42,87,88,92],[-53,92],[-67,73,88],[-87,11,42],[-92,11,42,53,73],[-57,20,81,84,91],[-65,20,76,84,89],[-84,12,57,65],[-89,12,45,65,81],[-91,12,45,57,76],[-13,14,22,25,29,30,71,72,75],[-14,13,22,25,28,29,71,74,75,77],[-28,14,71,72,75],[-30,13,71,74,75,77],[-72,13,25,28,29,74,75,77],[-74,14,22,29,30,72],[-77,14,22,25,30,71,72],[-28,17,79,82,84],[-46,13,74,78,79],[-74,17,37,46,47,82],[-78,17,37,43,46,79,82,84],[-82,13,28,43,47,74,78],[-84,13,28,37,47,78],[-18,13,28,60,61,77,78],[-28,18,89],[-54,13,77,78],[-77,18,54,61],[-78,18,54,60,89],[-89,13,28,61,78],[-14,16,39,47,48,83],[-16,14,30,47,48,78],[-30,16,83],[-39,14,78],[-78,16,39,48,83],[-83,14,30,47,78],[-30,85,88,90],[-72,56,61,90],[-78,52,56,85,88,90],[-88,14,30,56,61,78],[-15,16,22,34,37,39,71,72,79],[-16,15,22,34,37,38,71,79,80,82],[-38,16,71,72,79],[-39,15,71,79,80,82],[-72,15,34,37,38,79,80,82],[-80,16,22,37,39,72],[-82,16,22,34,39,71,72],[-38,17,75,77,84],[-46,15,75,80,83],[-80,17,29,46,48,77],[-83,17,29,44,46,75,77,84],[-84,15,29,38,48,83],[-19,15,38,68,69,82,83],[-38,19,91],[-63,15,82,83],[-82,19,63,69],[-83,19,63,68,91],[-91,15,38,69,83],[-16,52,64,69,85,88,92],[-72,64,69,92],[-83,52,64,85,88,92],[-88,16,39,64,69,83],[-17,20,60,68,70,89,91],[-46,20,89,91],[-70,17,77,82],[-77,20,68,70,91],[-82,20,60,70,89],[-89,17,46,68,82],[-91,17,46,60,77],[-18,25,49,55,56,71,75,85,86,90],[-54,71,75,85,86,90],[-74,49,55,56,85,86,90],[-86,18,25,54,55,56,74,75,89],[-89,25,49,56,71,85,86,90],[-90,18,25,49,54,55,71,74,75,89],[-49,-89,-90],[-71,-89,-90],[-54,20,79,84,91],[-70,18,74,79],[-74,20,62,70,91],[-84,18,54,62],[-91,18,43,54,74],[-80,49,62,64,85,86,92],[-86,19,34,62,63,64,79,80,91],[-92,19,34,49,62,63,71,79,80,91],[-63,20,75,84,89],[-70,19,75,80],[-80,20,55,70,89],[-84,19,55,63],[-89,19,44,63,80],[-21,71],[-71,21],[-22,49,52],[-49,22,52],[-52,22,49],[-24,73],[-73,24],[-25,34,43,44],[-34,25,43,44],[-43,25,34,44],[-44,25,34,43],[-27,75,76],[-75,27,76],[-76,27,75],[-29,55,60],[-55,29,60],[-60,29,55],[-35,79,81],[-79,35,81],[-81,35,79],[-37,62,68],[-62,37,68],[-68,37,62],[-47,61],[-61,47],[-48,69],[-69,48],[-87,50,85],[-56,64],[-64,56],[-86,88],[-88,86],[-90,92],[-92,90],[-93,1],[-1,93],[-94,2],[-2,94],[-95,3],[-3,95],[-96,4],[-4,96],[-97,5],[-5,97],[-98,6],[-6,98],[-99,7],[-7,99],[-100,8],[-8,100],[-101,9],[-9,101],[-10,102],[-103,11],[-11,103],[-104,12],[-12,104],[-13,105],[-106,14],[-14,106],[-107,15],[-15,107],[-16,108],[-17,109],[-18,110],[-19,111],[-20,112],[-113,93,94],[-94,113],[-93,113],[-93,-94,114],[-115,96,97],[-97,115],[-96,115],[-96,-97,116],[-117,95,115],[-115,117],[-95,117],[-95,-115,118],[-95,-116,119],[-120,113,117],[-117,120],[-118,121],[-119,122],[-113,120],[-113,-117,121],[-113,-118,122],[-113,-119,123],[-114,121],[-114,-117,122],[-114,-118,123],[-124,98,99],[-99,124],[-98,124],[-98,-99,125],[-102,126],[-127,101],[-101,126],[-101,-102,127],[-126,128],[-129,100,127],[-127,129],[-100,128],[-100,-126,129],[-100,-127,130],[-128,131],[-132,124,129],[-129,132],[-130,133],[-124,131],[-124,-128,132],[-125,132],[-125,-128,133],[-131,134],[-135,120,132],[-132,135],[-120,134],[-120,-131,135],[-120,-132,136],[-120,-133,137],[-121,135],[-121,-131,136],[-121,-132,137],[-122,136],[-122,-131,137],[-122,-132,138],[-123,137],[-123,-131,138],[-139,103,104],[-104,139],[-103,139],[-103,-104,140],[-141,106,107],[-107,141],[-106,141],[-106,-107,142],[-141,143],[-142,144],[-105,143],[-144,141],[-105,-141,144],[-143,145],[-146,139,144],[-144,146],[-139,145],[-139,-143,146],[-139,-144,147],[-140,146],[-140,-143,147],[-109,148],[-108,148],[-108,-109,149],[-112,150],[-111,150],[-111,-112,151],[-150,152],[-151,153],[-110,152],[-110,-150,153],[-110,-151,154],[-152,155],[-153,156],[-154,157],[-148,155],[-148,-152,156],[-148,-153,157],[-149,156],[-149,-152,157],[-155,158],[-156,159],[-157,160],[-145,158],[-145,-155,159],[-145,-156,160],[-145,-157,161],[-146,159],[-146,-155,160],[-146,-156,161],[-146,-157,162],[-147,-155,161],[-147,-156,162],[-162,163],[-134,-161,163],[-135,-160,163],[-136,-159,163],[-137,-158,163],[-138,163],[-163],[-164,51,58,59],[-51,164],[-58,164],[-59,164],[-165,66,67],[-66,165],[-67,165],[-166,23,33,42,53],[-33,166],[-42,166],[-53,166],[-167,28,30,32,78],[-28,167],[-30,167],[-32,167],[-78,167],[-168,39,72,83],[-39,168],[-72,168],[-83,168],[-169,31,57,77,89],[-31,169],[-57,169],[-77,169],[-89,169],[-170,36,38,40,41],[-36,170],[-38,170],[-40,170],[-41,170],[-171,46,54,63,70],[-46,171],[-54,171],[-63,171],[-70,171],[-172,26,45,74,80,84],[-45,172],[-74,172],[-80,172],[-173,65,82,91],[-65,173],[-82,173],[-91,173],[-174,164,165],[-175,164],[-175,165],[-164,-165,175],[-176,167,168],[-168,176],[-177,167],[-167,176],[-177,168],[-167,-168,177],[-178,166,176],[-179,166,177],[-180,166],[-179,176],[-166,-176,179],[-180,177],[-166,-177,180],[-181,174,180],[-182,174],[-181,175,179],[-182,175,180],[-183,175],[-181,178],[-182,179],[-175,-179,182],[-183,180],[-175,-180,183],[-184,169,170],[-185,169],[-169,184],[-185,170],[-169,-170,185],[-186,172,173],[-173,186],[-187,172],[-172,186],[-187,173],[-172,-173,187],[-188,171,186],[-189,171,187],[-187,189],[-190,171],[-189,186],[-171,-186,189],[-190,187],[-171,-187,190],[-191,184,190],[-192,184],[-191,185,189],[-192,185,190],[-184,-190,192],[-193,185],[-191,188],[-192,189],[-185,-189,192],[-193,190],[-185,-190,193],[-194,181],[-194,182,193],[-194,183,192],[-182,-193,195],[-194,191],[-183,-192,195],[194],[-195],[-50,196],[-86,196],[-90,196],[-85,197],[-88,197],[-92,197],[-198,21,22,24,87],[-21,198],[-22,198],[-24,198],[-87,198],[-199,49,71,73],[-49,199],[-71,199],[-73,199],[-200,25,27,35],[-25,200],[-27,200],[-35,200],[-201,34,75,79],[-34,201],[-75,201],[-79,201],[-202,43,76,81],[-43,202],[-76,202],[-81,202],[-203,29,37,44,47,48,52,56],[-29,203],[-37,203],[-44,203],[-47,203],[-48,203],[-52,203],[-56,203],[-204,55,61,62,64,69],[-55,204],[-61,204],[-62,204],[-64,204],[-69,204],[-205,60,68],[-60,205],[-68,205],[-197,206],[-196,206],[-196,-197,207],[-208,199,200],[-200,208],[-199,208],[-209,198,208],[-208,209],[-198,209],[-209,210],[-206,210],[-206,-209,211],[-207,-209,212],[-213,201,202],[-202,213],[-201,213],[-201,-202,214],[-215,204,205],[-205,215],[-204,215],[-204,-205,216],[-217,203,215],[-216,218],[-203,217],[-203,-215,218],[-219,213,217],[-217,219],[-218,220],[-213,219],[-213,-217,220],[-214,220],[-210,-220,221],[-211,-219,221],[-212,221],[-221],[-1,-10,-11,-16,-33,-41,-46,-58,-65,-78,-80,-86,-88,-89],[-1,-10,-11,-16,-33,-41,-45,-58,-63,-78,-82,-86,-88,-89],[-1,-10,-11,-16,-33,-41,-46,-58,-65,-78,-80,-85,-87,-89],[-1,-10,-11,-16,-33,-41,-45,-58,-63,-78,-82,-85,-87,-89],[-6,-7,-11,-19,-28,-33,-41,-45,-66,-72,-82,-89,-90,-92],[-6,-7,-11,-19,-31,-33,-41,-66,-70,-72,-74,-82,-90,-92],[-6,-7,-8,-18,-32,-40,-42,-66,-70,-72,-77,-80,-90,-92],[-7,-8,-12,-20,-32,-40,-42,-54,-66,-72,-77,-80,-90,-92],[-6,-7,-8,-18,-32,-38,-42,-45,-66,-72,-77,-90,-91,-92],[-1,-7,-11,-15,-33,-41,-45,-54,-66,-72,-77,-90,-91,-92],[-1,-2,-10,-16,-41,-45,-53,-58,-63,-78,-82,-89,-90,-92],[-1,-10,-11,-16,-33,-41,-45,-58,-63,-78,-82,-89,-90,-92],[-7,-14,-15,-16,-32,-41,-45,-53,-54,-66,-77,-90,-91,-92],[-1,-10,-11,-13,-33,-41,-45,-58,-63,-72,-82,-89,-90,-92],[-7,-8,-11,-15,-32,-41,-45,-54,-66,-72,-77,-90,-91,-92],[-1,-7,-11,-15,-33,-41,-46,-57,-66,-72,-74,-90,-91,-92],[-1,-2,-10,-16,-41,-46,-53,-58,-65,-78,-80,-89,-90,-92],[-1,-10,-11,-16,-33,-41,-46,-58,-65,-78,-80,-89,-90,-92],[-7,-14,-15,-16,-32,-41,-46,-53,-57,-66,-74,-90,-91,-92],[-1,-10,-11,-13,-33,-41,-46,-58,-65,-72,-80,-89,-90,-92],[-7,-8,-11,-15,-32,-41,-46,-57,-66,-72,-74,-90,-91,-92],[-5,-7,-8,-17,-32,-38,-42,-57,-66,-72,-74,-90,-91,-92],[-7,-16,-17,-20,-31,-33,-41,-54,-65,-67,-78,-80,-86,-88],[-7,-15,-16,-19,-31,-33,-41,-54,-65,-67,-78,-84,-86,-88],[-7,-15,-16,-19,-26,-33,-41,-46,-65,-67,-78,-86,-88,-89],[-1,-6,-7,-16,-33,-41,-46,-65,-67,-78,-80,-86,-88,-89],[-5,-7,-12,-16,-26,-33,-41,-63,-67,-78,-82,-86,-88,-89],[-1,-6,-7,-16,-33,-41,-45,-63,-67,-78,-82,-86,-88,-89],[-2,-10,-12,-17,-31,-36,-42,-54,-59,-78,-83,-86,-88,-91],[-1,-4,-7,-18,-33,-40,-57,-63,-67,-78,-83,-84,-86,-88],[-1,-2,-10,-18,-36,-42,-46,-57,-59,-78,-83,-86,-88,-91],[-1,-2,-10,-18,-40,-42,-57,-59,-63,-78,-83,-84,-86,-88],[-1,-4,-7,-18,-33,-36,-46,-57,-67,-78,-83,-86,-88,-91],[-2,-10,-12,-17,-26,-40,-42,-59,-63,-78,-83,-86,-88,-89],[-8,-13,-14,-18,-32,-36,-42,-46,-51,-57,-83,-90,-91,-92],[-1,-6,-11,-16,-33,-41,-46,-51,-65,-78,-80,-89,-90,-92],[-8,-14,-17,-20,-32,-40,-42,-51,-57,-63,-74,-83,-90,-92],[-8,-13,-14,-18,-32,-40,-42,-51,-57,-63,-83,-84,-90,-92],[-5,-8,-12,-14,-32,-36,-42,-51,-54,-77,-83,-90,-91,-92],[-1,-6,-11,-16,-33,-41,-45,-51,-63,-78,-82,-89,-90,-92],[-2,-8,-12,-17,-31,-36,-42,-51,-54,-78,-83,-90,-91,-92],[-1,-4,-11,-18,-33,-40,-51,-57,-63,-78,-83,-84,-90,-92],[-1,-2,-8,-18,-36,-42,-46,-51,-57,-78,-83,-90,-91,-92],[-1,-2,-8,-18,-40,-42,-51,-57,-63,-78,-83,-84,-90,-92],[-1,-4,-11,-18,-33,-36,-46,-51,-57,-78,-83,-90,-91,-92],[-2,-8,-12,-17,-26,-40,-42,-51,-63,-78,-83,-89,-90,-92],[-8,-14,-16,-18,-32,-38,-42,-45,-58,-66,-77,-86,-88,-91],[-8,-14,-16,-18,-32,-40,-42,-58,-66,-70,-77,-80,-86,-88],[-1,-11,-16,-19,-33,-41,-45,-58,-66,-78,-82,-86,-88,-89],[-1,-3,-8,-18,-30,-42,-45,-58,-66,-77,-83,-86,-88,-91],[-1,-11,-12,-16,-33,-41,-46,-58,-66,-78,-80,-86,-88,-89],[-1,-11,-12,-17,-33,-39,-40,-58,-66,-78,-80,-86,-88,-89],[-8,-14,-18,-19,-32,-40,-42,-58,-66,-70,-77,-83,-86,-88],[-8,-14,-17,-19,-32,-40,-42,-58,-66,-70,-74,-83,-86,-88],[-8,-14,-16,-18,-32,-38,-42,-45,-58,-66,-77,-85,-87,-91],[-8,-14,-16,-18,-32,-40,-42,-58,-66,-70,-77,-80,-85,-87],[-1,-11,-16,-19,-33,-41,-45,-58,-66,-78,-82,-85,-87,-89],[-1,-3,-8,-18,-30,-42,-45,-58,-66,-77,-83,-85,-87,-91],[-1,-11,-12,-16,-33,-41,-46,-58,-66,-78,-80,-85,-87,-89],[-1,-11,-12,-17,-33,-39,-40,-58,-66,-78,-80,-85,-87,-89],[-8,-14,-18,-19,-32,-40,-42,-58,-66,-70,-77,-83,-85,-87],[-8,-14,-17,-19,-32,-40,-42,-58,-66,-70,-74,-83,-85,-87],[-8,-18,-19,-20,-32,-38,-42,-45,-58,-66,-72,-77,-90,-92],[-8,-15,-18,-19,-32,-40,-42,-58,-66,-70,-72,-77,-90,-92],[-2,-16,-18,-19,-31,-41,-53,-58,-66,-70,-78,-82,-90,-92],[-8,-14,-18,-19,-32,-40,-42,-58,-66,-70,-77,-83,-90,-92],[-12,-14,-18,-20,-32,-39,-40,-53,-58,-66,-77,-80,-90,-92],[-8,-12,-18,-20,-32,-40,-42,-58,-66,-72,-77,-80,-90,-92],[-2,-16,-17,-18,-31,-41,-53,-58,-66,-70,-78,-80,-90,-92],[-8,-14,-17,-19,-32,-40,-42,-58,-66,-70,-74,-83,-90,-92],[-5,-14,-16,-18,-32,-41,-53,-58,-66,-70,-77,-80,-90,-92],[-2,-14,-16,-19,-31,-41,-53,-58,-66,-70,-74,-82,-90,-92],[-8,-14,-16,-18,-32,-40,-42,-58,-66,-70,-77,-80,-90,-92],[-8,-13,-17,-18,-32,-40,-42,-58,-66,-70,-72,-80,-90,-92],[-8,-15,-17,-19,-32,-40,-42,-58,-66,-70,-72,-74,-90,-92],[-1,-2,-8,-18,-40,-42,-58,-66,-70,-72,-77,-80,-90,-92],[-1,-5,-11,-18,-33,-41,-58,-66,-70,-72,-77,-80,-90,-92],[-1,-4,-11,-18,-33,-40,-58,-66,-70,-72,-77,-80,-90,-92],[-1,-5,-11,-19,-33,-41,-58,-66,-70,-72,-74,-82,-90,-92],[-5,-8,-11,-18,-32,-41,-58,-66,-70,-72,-77,-80,-90,-92],[-2,-8,-11,-19,-31,-41,-58,-66,-70,-72,-74,-82,-90,-92],[-5,-8,-12,-18,-32,-38,-42,-58,-66,-72,-77,-90,-91,-92],[-8,-13,-17,-19,-32,-38,-42,-45,-58,-66,-72,-89,-90,-92],[-8,-13,-17,-18,-32,-38,-42,-45,-58,-66,-72,-90,-91,-92],[-1,-2,-3,-19,-39,-45,-53,-58,-66,-78,-82,-89,-90,-92],[-1,-3,-8,-18,-30,-42,-45,-58,-66,-77,-83,-90,-91,-92],[-1,-15,-16,-18,-30,-41,-45,-53,-58,-66,-77,-90,-91,-92],[-1,-2,-8,-18,-38,-42,-45,-58,-66,-72,-77,-90,-91,-92],[-1,-11,-15,-18,-33,-41,-45,-58,-66,-72,-77,-90,-91,-92],[-1,-4,-11,-18,-33,-38,-45,-58,-66,-72,-77,-90,-91,-92],[-1,-11,-16,-19,-33,-41,-45,-58,-66,-78,-82,-89,-90,-92],[-8,-14,-16,-18,-32,-38,-42,-45,-58,-66,-77,-90,-91,-92],[-1,-2,-16,-19,-41,-45,-53,-58,-66,-78,-82,-89,-90,-92],[-1,-13,-16,-19,-30,-41,-45,-53,-58,-66,-82,-89,-90,-92],[-2,-14,-16,-19,-28,-41,-45,-53,-58,-66,-82,-89,-90,-92],[-13,-14,-16,-19,-32,-41,-45,-53,-58,-66,-82,-89,-90,-92],[-1,-11,-13,-19,-33,-41,-45,-58,-66,-72,-82,-89,-90,-92],[-8,-11,-13,-19,-32,-41,-45,-58,-66,-72,-82,-89,-90,-92],[-2,-8,-11,-19,-28,-41,-45,-58,-66,-72,-82,-89,-90,-92],[-5,-8,-12,-17,-32,-38,-42,-58,-66,-72,-74,-90,-91,-92],[-1,-2,-12,-17,-39,-40,-53,-58,-66,-78,-80,-89,-90,-92],[-1,-11,-12,-17,-33,-39,-40,-58,-66,-78,-80,-89,-90,-92],[-12,-13,-14,-17,-32,-39,-40,-53,-58,-66,-80,-89,-90,-92],[-2,-8,-12,-17,-31,-38,-42,-58,-66,-72,-74,-90,-91,-92],[-8,-12,-13,-17,-32,-40,-42,-58,-66,-72,-80,-89,-90,-92],[-2,-8,-12,-17,-28,-40,-42,-58,-66,-72,-80,-89,-90,-92],[-1,-2,-12,-16,-41,-46,-53,-58,-66,-78,-80,-89,-90,-92],[-1,-11,-12,-16,-33,-41,-46,-58,-66,-78,-80,-89,-90,-92],[-12,-13,-14,-16,-32,-41,-46,-53,-58,-66,-80,-89,-90,-92],[-1,-11,-12,-13,-33,-41,-46,-58,-66,-72,-80,-89,-90,-92],[-1,-11,-12,-15,-33,-41,-46,-58,-66,-72,-74,-90,-91,-92],[-8,-11,-12,-13,-32,-41,-46,-58,-66,-72,-80,-89,-90,-92],[-8,-13,-14,-16,-32,-41,-46,-58,-65,-67,-80,-86,-88,-89],[-8,-13,-14,-16,-32,-41,-45,-58,-63,-67,-82,-86,-88,-89],[-1,-2,-8,-16,-41,-46,-58,-65,-67,-78,-80,-86,-88,-89],[-1,-2,-8,-16,-41,-45,-58,-63,-67,-78,-82,-86,-88,-89],[-5,-14,-16,-17,-28,-33,-41,-58,-65,-67,-80,-86,-88,-89],[-1,-13,-14,-16,-33,-41,-46,-58,-65,-67,-80,-86,-88,-89],[-6,-14,-16,-18,-32,-38,-42,-45,-59,-66,-77,-86,-88,-91],[-1,-13,-14,-16,-33,-41,-45,-58,-63,-67,-82,-86,-88,-89],[-12,-14,-16,-20,-31,-33,-41,-58,-63,-67,-74,-82,-86,-88],[-6,-14,-16,-18,-32,-40,-42,-59,-66,-70,-77,-80,-86,-88],[-1,-16,-18,-20,-33,-41,-46,-58,-65,-67,-78,-80,-86,-88],[-1,-16,-18,-20,-33,-41,-45,-58,-63,-67,-78,-82,-86,-88],[-1,-4,-12,-18,-33,-36,-46,-58,-67,-78,-83,-86,-88,-91],[-1,-4,-12,-18,-33,-40,-58,-63,-67,-78,-83,-84,-86,-88],[-1,-9,-16,-19,-33,-41,-45,-58,-67,-78,-82,-86,-88,-89],[-1,-3,-6,-18,-30,-42,-45,-59,-66,-77,-83,-86,-88,-91],[-1,-4,-12,-19,-33,-36,-46,-58,-67,-78,-83,-86,-88,-89],[-1,-5,-12,-19,-33,-36,-39,-58,-67,-78,-82,-86,-88,-89],[-1,-15,-16,-19,-33,-41,-46,-58,-65,-67,-78,-86,-88,-89],[-1,-2,-3,-18,-42,-46,-57,-59,-66,-78,-83,-86,-88,-91],[-1,-4,-12,-17,-33,-40,-58,-63,-67,-78,-83,-86,-88,-89],[-1,-5,-12,-16,-33,-41,-58,-63,-67,-78,-82,-86,-88,-89],[-1,-15,-16,-17,-33,-41,-45,-58,-63,-67,-78,-86,-88,-89],[-1,-2,-3,-17,-42,-45,-54,-59,-66,-78,-83,-86,-88,-91],[-1,-2,-3,-14,-42,-45,-54,-59,-66,-77,-83,-86,-88,-91],[-1,-9,-12,-16,-33,-41,-46,-58,-67,-78,-80,-86,-88,-89],[-1,-9,-12,-17,-33,-39,-40,-58,-67,-78,-80,-86,-88,-89],[-1,-5,-16,-17,-33,-41,-58,-65,-67,-78,-80,-86,-88,-89],[-1,-2,-3,-14,-42,-46,-57,-59,-66,-74,-83,-86,-88,-91],[-1,-3,-5,-17,-30,-42,-57,-59,-66,-74,-83,-86,-88,-91],[-2,-12,-17,-19,-26,-40,-42,-59,-66,-78,-83,-86,-88,-89],[-12,-18,-19,-20,-26,-30,-40,-42,-59,-66,-77,-83,-86,-88],[-12,-13,-17,-19,-26,-30,-40,-42,-59,-66,-83,-86,-88,-89],[-12,-14,-19,-20,-32,-40,-42,-54,-59,-66,-77,-83,-86,-88],[-12,-13,-14,-19,-32,-40,-42,-54,-59,-66,-83,-84,-86,-88],[-1,-2,-12,-19,-40,-42,-54,-59,-66,-78,-83,-84,-86,-88],[-1,-2,-18,-19,-40,-42,-57,-59,-66,-78,-83,-84,-86,-88],[-1,-13,-18,-19,-30,-40,-42,-57,-59,-66,-83,-84,-86,-88],[-2,-14,-18,-19,-28,-40,-42,-57,-59,-66,-83,-84,-86,-88],[-13,-14,-18,-19,-32,-40,-42,-57,-59,-66,-83,-84,-86,-88],[-14,-17,-19,-20,-32,-40,-42,-57,-59,-66,-74,-83,-86,-88],[-1,-17,-19,-20,-30,-40,-42,-57,-59,-66,-74,-83,-86,-88],[-6,-14,-18,-19,-32,-40,-42,-59,-66,-70,-77,-83,-86,-88],[-6,-14,-17,-19,-32,-40,-42,-59,-66,-70,-74,-83,-86,-88],[-2,-17,-18,-19,-26,-40,-42,-59,-66,-70,-78,-83,-86,-88],[-2,-14,-18,-19,-26,-40,-42,-59,-66,-70,-77,-83,-86,-88],[-3,-7,-8,-14,-32,-42,-46,-57,-66,-74,-83,-86,-88,-91],[-3,-7,-8,-14,-32,-42,-45,-54,-66,-77,-83,-86,-88,-91],[-3,-7,-8,-14,-32,-42,-46,-57,-66,-74,-83,-85,-87,-91],[-3,-7,-8,-14,-32,-42,-45,-54,-66,-77,-83,-85,-87,-91],[-8,-9,-10,-18,-32,-38,-42,-45,-58,-72,-77,-90,-91,-92],[-8,-9,-10,-18,-32,-40,-42,-58,-70,-72,-77,-80,-90,-92],[-9,-10,-11,-19,-31,-33,-41,-58,-70,-72,-74,-82,-90,-92],[-10,-11,-12,-20,-31,-33,-41,-58,-63,-72,-74,-82,-90,-92],[-9,-10,-11,-19,-28,-33,-41,-45,-58,-72,-82,-89,-90,-92],[-3,-8,-10,-13,-32,-42,-45,-58,-63,-72,-82,-89,-90,-92],[-3,-4,-7,-14,-32,-45,-53,-54,-66,-77,-83,-90,-91,-92],[-3,-7,-8,-14,-32,-42,-45,-54,-66,-77,-83,-90,-91,-92],[-10,-13,-14,-16,-32,-41,-45,-53,-58,-63,-82,-89,-90,-92],[-3,-7,-8,-15,-32,-42,-45,-54,-66,-72,-77,-90,-91,-92],[-8,-10,-11,-13,-32,-41,-45,-58,-63,-72,-82,-89,-90,-92],[-3,-8,-10,-13,-32,-42,-46,-58,-65,-72,-80,-89,-90,-92],[-3,-4,-7,-14,-32,-46,-53,-57,-66,-74,-83,-90,-91,-92],[-3,-7,-8,-14,-32,-42,-46,-57,-66,-74,-83,-90,-91,-92],[-10,-13,-14,-16,-32,-41,-46,-53,-58,-65,-80,-89,-90,-92],[-3,-7,-8,-15,-32,-42,-46,-57,-66,-72,-74,-90,-91,-92],[-8,-10,-11,-13,-32,-41,-46,-58,-65,-72,-80,-89,-90,-92],[-5,-10,-11,-17,-28,-33,-41,-58,-65,-72,-80,-89,-90,-92],[-10,-14,-17,-20,-32,-40,-42,-57,-59,-63,-74,-83,-86,-88],[-10,-13,-14,-18,-32,-40,-42,-57,-59,-63,-83,-84,-86,-88],[-10,-13,-14,-18,-32,-36,-42,-46,-57,-59,-83,-86,-88,-91],[-3,-9,-10,-14,-32,-42,-46,-57,-59,-74,-83,-86,-88,-91],[-5,-10,-12,-14,-32,-36,-42,-54,-59,-77,-83,-86,-88,-91],[-3,-9,-10,-14,-32,-42,-45,-54,-59,-77,-83,-86,-88,-91],[-4,-7,-12,-17,-26,-33,-40,-63,-67,-78,-83,-86,-88,-89],[-2,-3,-10,-19,-31,-42,-54,-59,-65,-78,-83,-84,-86,-88],[-3,-4,-7,-19,-26,-33,-46,-65,-67,-78,-83,-86,-88,-89],[-3,-4,-7,-19,-31,-33,-54,-65,-67,-78,-83,-84,-86,-88],[-2,-3,-10,-19,-26,-42,-46,-59,-65,-78,-83,-86,-88,-89],[-4,-7,-12,-17,-31,-33,-36,-54,-67,-78,-83,-86,-88,-91],[-11,-15,-16,-19,-26,-33,-41,-46,-51,-65,-78,-89,-90,-92],[-3,-8,-9,-14,-32,-42,-46,-51,-57,-74,-83,-90,-91,-92],[-11,-16,-17,-20,-31,-33,-41,-51,-54,-65,-78,-80,-90,-92],[-11,-15,-16,-19,-31,-33,-41,-51,-54,-65,-78,-84,-90,-92],[-5,-11,-12,-16,-26,-33,-41,-51,-63,-78,-82,-89,-90,-92],[-3,-8,-9,-14,-32,-42,-45,-51,-54,-77,-83,-90,-91,-92],[-4,-11,-12,-17,-26,-33,-40,-51,-63,-78,-83,-89,-90,-92],[-2,-3,-8,-19,-31,-42,-51,-54,-65,-78,-83,-84,-90,-92],[-3,-4,-11,-19,-26,-33,-46,-51,-65,-78,-83,-89,-90,-92],[-3,-4,-11,-19,-31,-33,-51,-54,-65,-78,-83,-84,-90,-92],[-2,-3,-8,-19,-26,-42,-46,-51,-65,-78,-83,-89,-90,-92],[-4,-11,-12,-17,-31,-33,-36,-51,-54,-78,-83,-90,-91,-92],[-11,-14,-16,-19,-28,-33,-41,-45,-58,-66,-82,-86,-88,-89],[-11,-14,-16,-19,-31,-33,-41,-58,-66,-70,-74,-82,-86,-88],[-3,-8,-14,-18,-32,-42,-45,-58,-66,-77,-83,-86,-88,-91],[-1,-3,-11,-19,-33,-39,-45,-58,-66,-78,-82,-86,-88,-89],[-3,-8,-12,-14,-32,-42,-46,-58,-66,-74,-83,-86,-88,-91],[-3,-8,-12,-17,-30,-31,-42,-58,-66,-74,-83,-86,-88,-91],[-11,-16,-18,-19,-31,-33,-41,-58,-66,-70,-78,-82,-86,-88],[-11,-16,-17,-18,-31,-33,-41,-58,-66,-70,-78,-80,-86,-88],[-11,-14,-16,-19,-28,-33,-41,-45,-58,-66,-82,-85,-87,-89],[-11,-14,-16,-19,-31,-33,-41,-58,-66,-70,-74,-82,-85,-87],[-3,-8,-14,-18,-32,-42,-45,-58,-66,-77,-83,-85,-87,-91],[-1,-3,-11,-19,-33,-39,-45,-58,-66,-78,-82,-85,-87,-89],[-3,-8,-12,-14,-32,-42,-46,-58,-66,-74,-83,-85,-87,-91],[-3,-8,-12,-17,-30,-31,-42,-58,-66,-74,-83,-85,-87,-91],[-11,-16,-18,-19,-31,-33,-41,-58,-66,-70,-78,-82,-85,-87],[-11,-16,-17,-18,-31,-33,-41,-58,-66,-70,-78,-80,-85,-87],[-11,-18,-19,-20,-28,-33,-41,-45,-58,-66,-72,-82,-90,-92],[-11,-13,-18,-19,-31,-33,-41,-58,-66,-70,-72,-82,-90,-92],[-4,-14,-18,-19,-32,-40,-53,-58,-66,-70,-77,-83,-90,-92],[-11,-16,-18,-19,-31,-33,-41,-58,-66,-70,-78,-82,-90,-92],[-12,-16,-19,-20,-30,-31,-41,-53,-58,-66,-74,-82,-90,-92],[-11,-12,-19,-20,-31,-33,-41,-58,-66,-72,-74,-82,-90,-92],[-4,-14,-17,-19,-32,-40,-53,-58,-66,-70,-74,-83,-90,-92],[-11,-16,-17,-18,-31,-33,-41,-58,-66,-70,-78,-80,-90,-92],[-5,-14,-16,-19,-32,-41,-53,-58,-66,-70,-74,-82,-90,-92],[-4,-14,-16,-18,-32,-40,-53,-58,-66,-70,-77,-80,-90,-92],[-11,-14,-16,-19,-31,-33,-41,-58,-66,-70,-74,-82,-90,-92],[-11,-15,-17,-19,-31,-33,-41,-58,-66,-70,-72,-74,-90,-92],[-11,-13,-17,-18,-31,-33,-41,-58,-66,-70,-72,-80,-90,-92],[-3,-4,-11,-19,-31,-33,-58,-66,-70,-72,-74,-82,-90,-92],[-3,-5,-8,-19,-32,-42,-58,-66,-70,-72,-74,-82,-90,-92],[-2,-3,-8,-19,-31,-42,-58,-66,-70,-72,-74,-82,-90,-92],[-3,-5,-8,-18,-32,-42,-58,-66,-70,-72,-77,-80,-90,-92],[-5,-8,-11,-19,-32,-41,-58,-66,-70,-72,-74,-82,-90,-92],[-4,-8,-11,-18,-32,-40,-58,-66,-70,-72,-77,-80,-90,-92],[-5,-11,-12,-19,-28,-33,-41,-58,-66,-72,-82,-89,-90,-92],[-11,-15,-17,-18,-28,-33,-41,-45,-58,-66,-72,-90,-91,-92],[-11,-15,-17,-19,-28,-33,-41,-45,-58,-66,-72,-89,-90,-92],[-1,-3,-4,-18,-30,-45,-53,-58,-66,-77,-83,-90,-91,-92],[-1,-3,-11,-19,-33,-39,-45,-58,-66,-78,-82,-89,-90,-92],[-3,-13,-14,-19,-32,-39,-45,-53,-58,-66,-82,-89,-90,-92],[-3,-4,-11,-19,-28,-33,-45,-58,-66,-72,-82,-89,-90,-92],[-3,-8,-13,-19,-32,-42,-45,-58,-66,-72,-82,-89,-90,-92],[-2,-3,-8,-19,-28,-42,-45,-58,-66,-72,-82,-89,-90,-92],[-3,-8,-14,-18,-32,-42,-45,-58,-66,-77,-83,-90,-91,-92],[-11,-14,-16,-19,-28,-33,-41,-45,-58,-66,-82,-89,-90,-92],[-3,-4,-14,-18,-32,-45,-53,-58,-66,-77,-83,-90,-91,-92],[-3,-14,-15,-18,-32,-39,-45,-53,-58,-66,-77,-90,-91,-92],[-4,-14,-16,-18,-32,-38,-45,-53,-58,-66,-77,-90,-91,-92],[-14,-15,-16,-18,-32,-41,-45,-53,-58,-66,-77,-90,-91,-92],[-3,-8,-15,-18,-32,-42,-45,-58,-66,-72,-77,-90,-91,-92],[-8,-11,-15,-18,-32,-41,-45,-58,-66,-72,-77,-90,-91,-92],[-4,-8,-11,-18,-32,-38,-45,-58,-66,-72,-77,-90,-91,-92],[-5,-11,-12,-17,-28,-33,-41,-58,-66,-72,-80,-89,-90,-92],[-3,-4,-12,-17,-30,-31,-53,-58,-66,-74,-83,-90,-91,-92],[-3,-8,-12,-17,-30,-31,-42,-58,-66,-74,-83,-90,-91,-92],[-12,-15,-16,-17,-30,-31,-41,-53,-58,-66,-74,-90,-91,-92],[-4,-11,-12,-17,-28,-33,-40,-58,-66,-72,-80,-89,-90,-92],[-11,-12,-15,-17,-31,-33,-41,-58,-66,-72,-74,-90,-91,-92],[-4,-11,-12,-17,-31,-33,-38,-58,-66,-72,-74,-90,-91,-92],[-3,-4,-12,-14,-32,-46,-53,-58,-66,-74,-83,-90,-91,-92],[-3,-8,-12,-14,-32,-42,-46,-58,-66,-74,-83,-90,-91,-92],[-12,-14,-15,-16,-32,-41,-46,-53,-58,-66,-74,-90,-91,-92],[-3,-8,-12,-15,-32,-42,-46,-58,-66,-72,-74,-90,-91,-92],[-3,-8,-12,-13,-32,-42,-46,-58,-66,-72,-80,-89,-90,-92],[-8,-11,-12,-15,-32,-41,-46,-58,-66,-72,-74,-90,-91,-92],[-11,-14,-15,-16,-32,-41,-46,-57,-59,-66,-74,-86,-88,-91],[-11,-14,-15,-16,-32,-41,-45,-54,-59,-66,-77,-86,-88,-91],[-3,-4,-11,-14,-32,-46,-57,-59,-66,-74,-83,-86,-88,-91],[-3,-4,-11,-14,-32,-45,-54,-59,-66,-77,-83,-86,-88,-91],[-5,-14,-16,-17,-32,-38,-42,-57,-59,-66,-74,-86,-88,-91],[-3,-14,-15,-16,-32,-42,-46,-57,-59,-66,-74,-86,-88,-91],[-9,-14,-16,-19,-28,-33,-41,-45,-58,-67,-82,-86,-88,-89],[-3,-14,-15,-16,-32,-42,-45,-54,-59,-66,-77,-86,-88,-91],[-12,-14,-16,-20,-32,-40,-42,-54,-59,-66,-77,-80,-86,-88],[-9,-14,-16,-19,-31,-33,-41,-58,-67,-70,-74,-82,-86,-88],[-3,-14,-19,-20,-32,-42,-46,-57,-59,-66,-74,-83,-86,-88],[-3,-14,-19,-20,-32,-42,-45,-54,-59,-66,-77,-83,-86,-88],[-2,-3,-12,-19,-26,-42,-46,-59,-66,-78,-83,-86,-88,-89],[-2,-3,-12,-19,-31,-42,-54,-59,-66,-78,-83,-84,-86,-88],[-3,-6,-14,-18,-32,-42,-45,-59,-66,-77,-83,-86,-88,-91],[-1,-3,-9,-19,-33,-39,-45,-58,-67,-78,-82,-86,-88,-89],[-2,-3,-12,-18,-26,-42,-46,-59,-66,-78,-83,-86,-88,-91],[-3,-5,-12,-18,-26,-30,-42,-59,-66,-77,-83,-86,-88,-91],[-3,-13,-14,-18,-32,-42,-46,-57,-59,-66,-83,-86,-88,-91],[-1,-3,-4,-19,-33,-46,-58,-65,-67,-78,-83,-86,-88,-89],[-2,-3,-12,-17,-31,-42,-54,-59,-66,-78,-83,-86,-88,-91],[-3,-5,-12,-14,-32,-42,-54,-59,-66,-77,-83,-86,-88,-91],[-3,-13,-14,-17,-32,-42,-45,-54,-59,-66,-83,-86,-88,-91],[-1,-3,-4,-17,-33,-45,-58,-63,-67,-78,-83,-86,-88,-89],[-1,-3,-4,-16,-33,-45,-58,-63,-67,-78,-82,-86,-88,-89],[-3,-6,-12,-14,-32,-42,-46,-59,-66,-74,-83,-86,-88,-91],[-3,-6,-12,-17,-30,-31,-42,-59,-66,-74,-83,-86,-88,-91],[-3,-5,-14,-17,-32,-42,-57,-59,-66,-74,-83,-86,-88,-91],[-1,-3,-4,-16,-33,-46,-58,-65,-67,-78,-80,-86,-88,-89],[-1,-3,-5,-17,-33,-39,-58,-65,-67,-78,-80,-86,-88,-89],[-4,-12,-17,-18,-31,-33,-36,-58,-67,-78,-83,-86,-88,-91],[-12,-18,-19,-20,-31,-33,-36,-39,-58,-67,-78,-82,-86,-88],[-12,-15,-17,-18,-31,-33,-36,-39,-58,-67,-78,-86,-88,-91],[-12,-16,-18,-20,-31,-33,-41,-58,-63,-67,-78,-82,-86,-88],[-12,-15,-16,-18,-31,-33,-41,-58,-63,-67,-78,-84,-86,-88],[-3,-4,-12,-18,-31,-33,-58,-63,-67,-78,-83,-84,-86,-88],[-3,-4,-18,-19,-31,-33,-58,-65,-67,-78,-83,-84,-86,-88],[-3,-15,-18,-19,-31,-33,-39,-58,-65,-67,-78,-84,-86,-88],[-4,-16,-18,-19,-31,-33,-38,-58,-65,-67,-78,-84,-86,-88],[-15,-16,-18,-19,-31,-33,-41,-58,-65,-67,-78,-84,-86,-88],[-16,-17,-18,-20,-31,-33,-41,-58,-65,-67,-78,-80,-86,-88],[-3,-17,-18,-20,-31,-33,-39,-58,-65,-67,-78,-80,-86,-88],[-9,-16,-18,-19,-31,-33,-41,-58,-67,-70,-78,-82,-86,-88],[-9,-16,-17,-18,-31,-33,-41,-58,-67,-70,-78,-80,-86,-88],[-4,-17,-18,-19,-31,-33,-36,-58,-67,-70,-78,-83,-86,-88],[-4,-16,-18,-19,-31,-33,-36,-58,-67,-70,-78,-82,-86,-88],[7,8,10,11,24,33,42,51,53,58,59,66,67],[7,8,24,33,51,53,58,59,73,86,87,88,90],[7,10,51,58,59,66,67,86,87,90,92],[8,11,33,42,53,59,67,73,87,88,90,92]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":1,\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":3,\"kind\":1},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":22,\"b\":1},{\"tag\":\"incompatible\",\"a\":25,\"b\":0},{\"tag\":\"incompatible\",\"a\":27,\"b\":0},{\"tag\":\"incompatible\",\"a\":27,\"b\":25},{\"tag\":\"incompatible\",\"a\":29,\"b\":1},{\"tag\":\"incompatible\",\"a\":29,\"b\":22},{\"tag\":\"incompatible\",\"a\":29,\"b\":27},{\"tag\":\"incompatible\",\"a\":30,\"b\":0},{\"tag\":\"incompatible\",\"a\":30,\"b\":25},{\"tag\":\"incompatible\",\"a\":30,\"b\":27},{\"tag\":\"incompatible\",\"a\":31,\"b\":1},{\"tag\":\"incompatible\",\"a\":31,\"b\":20},{\"tag\":\"incompatible\",\"a\":31,\"b\":21},{\"tag\":\"incompatible\",\"a\":31,\"b\":22},{\"tag\":\"incompatible\",\"a\":31,\"b\":23},{\"tag\":\"incompatible\",\"a\":31,\"b\":25},{\"tag\":\"incompatible\",\"a\":31,\"b\":27},{\"tag\":\"incompatible\",\"a\":31,\"b\":29},{\"tag\":\"incompatible\",\"a\":31,\"b\":30},{\"tag\":\"incompatible\",\"a\":32,\"b\":1},{\"tag\":\"incompatible\",\"a\":32,\"b\":23},{\"tag\":\"incompatible\",\"a\":32,\"b\":29},{\"tag\":\"incompatible\",\"a\":32,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":20},{\"tag\":\"incompatible\",\"a\":35,\"b\":25},{\"tag\":\"incompatible\",\"a\":37,\"b\":2},{\"tag\":\"incompatible\",\"a\":37,\"b\":14},{\"tag\":\"incompatible\",\"a\":37,\"b\":21},{\"tag\":\"incompatible\",\"a\":37,\"b\":27},{\"tag\":\"incompatible\",\"a\":37,\"b\":29},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":22},{\"tag\":\"incompatible\",\"a\":38,\"b\":27},{\"tag\":\"incompatible\",\"a\":38,\"b\":29},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":2},{\"tag\":\"incompatible\",\"a\":39,\"b\":4},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":2},{\"tag\":\"incompatible\",\"a\":40,\"b\":20},{\"tag\":\"incompatible\",\"a\":40,\"b\":21},{\"tag\":\"incompatible\",\"a\":40,\"b\":22},{\"tag\":\"incompatible\",\"a\":40,\"b\":23},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":3},{\"tag\":\"incompatible\",\"a\":41,\"b\":22},{\"tag\":\"incompatible\",\"a\":41,\"b\":23},{\"tag\":\"incompatible\",\"a\":41,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":20},{\"tag\":\"incompatible\",\"a\":44,\"b\":25},{\"tag\":\"incompatible\",\"a\":44,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":21},{\"tag\":\"incompatible\",\"a\":45,\"b\":27},{\"tag\":\"incompatible\",\"a\":45,\"b\":29},{\"tag\":\"incompatible\",\"a\":45,\"b\":30},{\"tag\":\"incompatible\",\"a\":45,\"b\":37},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":48,\"b\":29},{\"tag\":\"incompatible\",\"a\":49,\"b\":41},{\"tag\":\"incompatible\",\"a\":50,\"b\":20},{\"tag\":\"incompatible\",\"a\":50,\"b\":21},{\"tag\":\"incompatible\",\"a\":50,\"b\":22},{\"tag\":\"incompatible\",\"a\":50,\"b\":23},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":20},{\"tag\":\"incompatible\",\"a\":52,\"b\":21},{\"tag\":\"incompatible\",\"a\":52,\"b\":22},{\"tag\":\"incompatible\",\"a\":52,\"b\":23},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":17},{\"tag\":\"incompatible\",\"a\":53,\"b\":21},{\"tag\":\"incompatible\",\"a\":53,\"b\":25},{\"tag\":\"incompatible\",\"a\":53,\"b\":27},{\"tag\":\"incompatible\",\"a\":53,\"b\":29},{\"tag\":\"incompatible\",\"a\":53,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":38},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":56,\"b\":5},{\"tag\":\"incompatible\",\"a\":56,\"b\":25},{\"tag\":\"incompatible\",\"a\":56,\"b\":30},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":20},{\"tag\":\"incompatible\",\"a\":57,\"b\":25},{\"tag\":\"incompatible\",\"a\":57,\"b\":48},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":6},{\"tag\":\"incompatible\",\"a\":58,\"b\":7},{\"tag\":\"incompatible\",\"a\":58,\"b\":23},{\"tag\":\"incompatible\",\"a\":58,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":49},{\"tag\":\"incompatible\",\"a\":58,\"b\":52},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":8},{\"tag\":\"incompatible\",\"a\":62,\"b\":21},{\"tag\":\"incompatible\",\"a\":62,\"b\":27},{\"tag\":\"incompatible\",\"a\":62,\"b\":29},{\"tag\":\"incompatible\",\"a\":62,\"b\":35},{\"tag\":\"incompatible\",\"a\":62,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":45},{\"tag\":\"incompatible\",\"a\":62,\"b\":48},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":64,\"b\":11},{\"tag\":\"incompatible\",\"a\":64,\"b\":35},{\"tag\":\"incompatible\",\"a\":64,\"b\":39},{\"tag\":\"incompatible\",\"a\":64,\"b\":44},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":20},{\"tag\":\"incompatible\",\"a\":65,\"b\":35},{\"tag\":\"incompatible\",\"a\":65,\"b\":48},{\"tag\":\"incompatible\",\"a\":65,\"b\":49},{\"tag\":\"incompatible\",\"a\":65,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":23},{\"tag\":\"incompatible\",\"a\":66,\"b\":41},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":66,\"b\":52},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":27},{\"tag\":\"incompatible\",\"a\":69,\"b\":29},{\"tag\":\"incompatible\",\"a\":69,\"b\":37},{\"tag\":\"incompatible\",\"a\":69,\"b\":38},{\"tag\":\"incompatible\",\"a\":69,\"b\":44},{\"tag\":\"incompatible\",\"a\":69,\"b\":45},{\"tag\":\"incompatible\",\"a\":69,\"b\":53},{\"tag\":\"incompatible\",\"a\":69,\"b\":56},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":50},{\"tag\":\"incompatible\",\"a\":70,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":13},{\"tag\":\"incompatible\",\"a\":71,\"b\":15},{\"tag\":\"incompatible\",\"a\":71,\"b\":20},{\"tag\":\"incompatible\",\"a\":71,\"b\":22},{\"tag\":\"incompatible\",\"a\":71,\"b\":29},{\"tag\":\"incompatible\",\"a\":71,\"b\":38},{\"tag\":\"incompatible\",\"a\":71,\"b\":49},{\"tag\":\"incompatible\",\"a\":71,\"b\":50},{\"tag\":\"incompatible\",\"a\":71,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":29},{\"tag\":\"incompatible\",\"a\":72,\"b\":32},{\"tag\":\"incompatible\",\"a\":72,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":41},{\"tag\":\"incompatible\",\"a\":72,\"b\":50},{\"tag\":\"incompatible\",\"a\":72,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":25},{\"tag\":\"incompatible\",\"a\":73,\"b\":27},{\"tag\":\"incompatible\",\"a\":73,\"b\":35},{\"tag\":\"incompatible\",\"a\":73,\"b\":44},{\"tag\":\"incompatible\",\"a\":73,\"b\":53},{\"tag\":\"incompatible\",\"a\":76,\"b\":12},{\"tag\":\"incompatible\",\"a\":76,\"b\":27},{\"tag\":\"incompatible\",\"a\":76,\"b\":30},{\"tag\":\"incompatible\",\"a\":76,\"b\":45},{\"tag\":\"incompatible\",\"a\":76,\"b\":56},{\"tag\":\"incompatible\",\"a\":76,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":21},{\"tag\":\"incompatible\",\"a\":77,\"b\":27},{\"tag\":\"incompatible\",\"a\":77,\"b\":29},{\"tag\":\"incompatible\",\"a\":77,\"b\":31},{\"tag\":\"incompatible\",\"a\":77,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":14},{\"tag\":\"incompatible\",\"a\":79,\"b\":18},{\"tag\":\"incompatible\",\"a\":79,\"b\":25},{\"tag\":\"incompatible\",\"a\":79,\"b\":35},{\"tag\":\"incompatible\",\"a\":79,\"b\":37},{\"tag\":\"incompatible\",\"a\":79,\"b\":44},{\"tag\":\"incompatible\",\"a\":79,\"b\":62},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":81,\"b\":37},{\"tag\":\"incompatible\",\"a\":81,\"b\":39},{\"tag\":\"incompatible\",\"a\":81,\"b\":45},{\"tag\":\"incompatible\",\"a\":81,\"b\":64},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":21},{\"tag\":\"incompatible\",\"a\":82,\"b\":37},{\"tag\":\"incompatible\",\"a\":82,\"b\":38},{\"tag\":\"incompatible\",\"a\":82,\"b\":40},{\"tag\":\"incompatible\",\"a\":82,\"b\":70},{\"tag\":\"incompatible\",\"a\":82,\"b\":71},{\"tag\":\"incompatible\",\"a\":82,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":16},{\"tag\":\"incompatible\",\"a\":83,\"b\":25},{\"tag\":\"incompatible\",\"a\":83,\"b\":35},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":45},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":83,\"b\":73},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":84,\"b\":58},{\"tag\":\"incompatible\",\"a\":84,\"b\":66},{\"tag\":\"incompatible\",\"a\":85,\"b\":21},{\"tag\":\"incompatible\",\"a\":85,\"b\":22},{\"tag\":\"incompatible\",\"a\":85,\"b\":23},{\"tag\":\"incompatible\",\"a\":85,\"b\":49},{\"tag\":\"incompatible\",\"a\":85,\"b\":50},{\"tag\":\"incompatible\",\"a\":85,\"b\":70},{\"tag\":\"incompatible\",\"a\":85,\"b\":71},{\"tag\":\"incompatible\",\"a\":86,\"b\":50},{\"tag\":\"incompatible\",\"a\":86,\"b\":58},{\"tag\":\"incompatible\",\"a\":86,\"b\":71},{\"tag\":\"incompatible\",\"a\":88,\"b\":17},{\"tag\":\"incompatible\",\"a\":88,\"b\":30},{\"tag\":\"incompatible\",\"a\":88,\"b\":53},{\"tag\":\"incompatible\",\"a\":88,\"b\":56},{\"tag\":\"incompatible\",\"a\":88,\"b\":69},{\"tag\":\"incompatible\",\"a\":88,\"b\":73},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":89,\"b\":58},{\"tag\":\"incompatible\",\"a\":89,\"b\":66},{\"tag\":\"incompatible\",\"a\":90,\"b\":39},{\"tag\":\"incompatible\",\"a\":90,\"b\":62},{\"tag\":\"incompatible\",\"a\":90,\"b\":64},{\"tag\":\"incompatible\",\"a\":90,\"b\":69},{\"tag\":\"incompatible\",\"a\":90,\"b\":79},{\"tag\":\"incompatible\",\"a\":90,\"b\":81},{\"tag\":\"incompatible\",\"a\":90,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":66},{\"tag\":\"mate\",\"ridge\":7,\"a\":0,\"owners\":[1,20,21,22,23,24,26,28,29,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":1,\"owners\":[0,20,21,23,24,25,26,27,28,30]},{\"tag\":\"mate\",\"ridge\":7,\"a\":25,\"owners\":[1,21,22,23,28,29,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":27,\"owners\":[1,20,22,23,26,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":29,\"owners\":[0,20,23,25,26,30]},{\"tag\":\"mate\",\"ridge\":7,\"a\":30,\"owners\":[1,20,21,22,23,24,29,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":32,\"owners\":[0,20,21,24,25,26,27,28,30]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[0,1,23]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[1,23,25]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[1,23,30]},{\"tag\":\"mate\",\"ridge\":67,\"a\":25,\"owners\":[4,36,39,45,46]},{\"tag\":\"mate\",\"ridge\":67,\"a\":27,\"owners\":[4,34,39,44]},{\"tag\":\"mate\",\"ridge\":67,\"a\":31,\"owners\":[4,34,36,39,42,44,45]},{\"tag\":\"mate\",\"ridge\":67,\"a\":39,\"owners\":[0,25,27,31,42,46]},{\"tag\":\"mate\",\"ridge\":67,\"a\":44,\"owners\":[0,27,31,36,46]},{\"tag\":\"mate\",\"ridge\":67,\"a\":45,\"owners\":[0,25,31,34]},{\"tag\":\"mate\",\"ridge\":69,\"a\":27,\"owners\":[5,56,57]},{\"tag\":\"mate\",\"ridge\":69,\"a\":30,\"owners\":[5,53,57,60]},{\"tag\":\"mate\",\"ridge\":69,\"a\":31,\"owners\":[5,53,56,57,59]},{\"tag\":\"mate\",\"ridge\":69,\"a\":53,\"owners\":[0,30,31]},{\"tag\":\"mate\",\"ridge\":69,\"a\":56,\"owners\":[0,27,31,60]},{\"tag\":\"mate\",\"ridge\":69,\"a\":57,\"owners\":[0,27,30,31,59,60]},{\"tag\":\"mate\",\"ridge\":70,\"a\":0,\"owners\":[12,73,75,76,77]},{\"tag\":\"mate\",\"ridge\":70,\"a\":30,\"owners\":[12,73,77]},{\"tag\":\"mate\",\"ridge\":70,\"a\":31,\"owners\":[12,73,75,76]},{\"tag\":\"mate\",\"ridge\":70,\"a\":73,\"owners\":[0,30,31]},{\"tag\":\"mate\",\"ridge\":70,\"a\":76,\"owners\":[0,25,31]},{\"tag\":\"mate\",\"ridge\":70,\"a\":77,\"owners\":[0,25,30,75]},{\"tag\":\"mate\",\"ridge\":259,\"a\":1,\"owners\":[3,38,40,41,46,47]},{\"tag\":\"mate\",\"ridge\":259,\"a\":31,\"owners\":[3,38,40,41,47]},{\"tag\":\"mate\",\"ridge\":259,\"a\":32,\"owners\":[3,38,40,46,47]},{\"tag\":\"mate\",\"ridge\":259,\"a\":38,\"owners\":[1,31,32]},{\"tag\":\"mate\",\"ridge\":259,\"a\":40,\"owners\":[1,29,31,32,46]},{\"tag\":\"mate\",\"ridge\":259,\"a\":41,\"owners\":[1,29,31,46,47]},{\"tag\":\"mate\",\"ridge\":261,\"a\":1,\"owners\":[7,49,51,52,55,58,60]},{\"tag\":\"mate\",\"ridge\":261,\"a\":7,\"owners\":[1,22,29,31,49,51,55,60]},{\"tag\":\"mate\",\"ridge\":261,\"a\":22,\"owners\":[7,55,58,60]},{\"tag\":\"mate\",\"ridge\":261,\"a\":31,\"owners\":[7,49,51,52,55,58]},{\"tag\":\"mate\",\"ridge\":261,\"a\":52,\"owners\":[1,29,31,55,60]},{\"tag\":\"mate\",\"ridge\":261,\"a\":58,\"owners\":[1,22,29,31,51,60]},{\"tag\":\"mate\",\"ridge\":262,\"a\":1,\"owners\":[13,71,72,77]},{\"tag\":\"mate\",\"ridge\":262,\"a\":31,\"owners\":[13,71,72]},{\"tag\":\"mate\",\"ridge\":262,\"a\":32,\"owners\":[13,71,77]},{\"tag\":\"mate\",\"ridge\":262,\"a\":71,\"owners\":[1,31,32]},{\"tag\":\"mate\",\"ridge\":262,\"a\":77,\"owners\":[1,22,32,72]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[1,72,77]},{\"tag\":\"mate\",\"ridge\":11,\"a\":3,\"owners\":[2,20,21,23,33,34,35,36,37,39]},{\"tag\":\"mate\",\"ridge\":11,\"a\":22,\"owners\":[2,33,34,35,36,37,39]},{\"tag\":\"mate\",\"ridge\":11,\"a\":35,\"owners\":[3,21,22,23,36,38,41]},{\"tag\":\"mate\",\"ridge\":11,\"a\":37,\"owners\":[3,20,22,23,34,41]},{\"tag\":\"mate\",\"ridge\":11,\"a\":38,\"owners\":[2,20,23,34,35,39]},{\"tag\":\"mate\",\"ridge\":11,\"a\":39,\"owners\":[3,20,21,22,23,33,38,41]},{\"tag\":\"mate\",\"ridge\":11,\"a\":41,\"owners\":[2,20,21,33,34,35,36,37,39]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[2,3,23]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[20,39,41]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[21,35,41]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[21,39,41]},{\"tag\":\"mate\",\"ridge\":131,\"a\":2,\"owners\":[4,26,28,30,43,44,45,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":4,\"owners\":[2,26,28,35,37,40,43,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":30,\"owners\":[2,35,37,40,43,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":35,\"owners\":[4,28,30,45,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":40,\"owners\":[4,26,28,30,43,44,45]},{\"tag\":\"mate\",\"ridge\":131,\"a\":44,\"owners\":[2,28,37,40,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":45,\"owners\":[2,26,35,40]},{\"tag\":\"mate\",\"ridge\":137,\"a\":39,\"owners\":[8,62,65,68]},{\"tag\":\"mate\",\"ridge\":137,\"a\":40,\"owners\":[8,62,64,65,67]},{\"tag\":\"mate\",\"ridge\":137,\"a\":64,\"owners\":[2,37,40,68]},{\"tag\":\"mate\",\"ridge\":137,\"a\":65,\"owners\":[2,37,39,40,67,68]},{\"tag\":\"mate\",\"ridge\":138,\"a\":35,\"owners\":[14,81,82]},{\"tag\":\"mate\",\"ridge\":138,\"a\":39,\"owners\":[14,79,82]},{\"tag\":\"mate\",\"ridge\":138,\"a\":40,\"owners\":[14,79,80,81]},{\"tag\":\"mate\",\"ridge\":138,\"a\":79,\"owners\":[2,39,40]},{\"tag\":\"mate\",\"ridge\":138,\"a\":81,\"owners\":[2,35,40]},{\"tag\":\"mate\",\"ridge\":138,\"a\":82,\"owners\":[2,35,39,80]},{\"tag\":\"mate\",\"ridge\":265,\"a\":10,\"owners\":[3,22,38,40,49,51,63,68]},{\"tag\":\"mate\",\"ridge\":265,\"a\":40,\"owners\":[10,49,51,52,63,66]},{\"tag\":\"mate\",\"ridge\":265,\"a\":52,\"owners\":[3,38,40,63,68]},{\"tag\":\"mate\",\"ridge\":265,\"a\":66,\"owners\":[3,22,38,40,51,68]},{\"tag\":\"mate\",\"ridge\":266,\"a\":40,\"owners\":[15,71,72]},{\"tag\":\"mate\",\"ridge\":266,\"a\":41,\"owners\":[15,71,82]},{\"tag\":\"mate\",\"ridge\":266,\"a\":71,\"owners\":[3,40,41]},{\"tag\":\"mate\",\"ridge\":266,\"a\":82,\"owners\":[3,22,41,72]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[15,40,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":11,\"owners\":[4,30,39,45,59,67]},{\"tag\":\"mate\",\"ridge\":193,\"a\":30,\"owners\":[11,64,67,69]},{\"tag\":\"mate\",\"ridge\":193,\"a\":39,\"owners\":[11,56,59,69]},{\"tag\":\"mate\",\"ridge\":193,\"a\":45,\"owners\":[11,56,64]},{\"tag\":\"mate\",\"ridge\":193,\"a\":56,\"owners\":[4,39,45,67]},{\"tag\":\"mate\",\"ridge\":193,\"a\":64,\"owners\":[4,30,45,59]},{\"tag\":\"mate\",\"ridge\":193,\"a\":69,\"owners\":[4,30,39]},{\"tag\":\"mate\",\"ridge\":194,\"a\":30,\"owners\":[16,80,81,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":39,\"owners\":[16,75,76,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":44,\"owners\":[16,76,81]},{\"tag\":\"mate\",\"ridge\":194,\"a\":76,\"owners\":[4,39,44,80]},{\"tag\":\"mate\",\"ridge\":194,\"a\":81,\"owners\":[4,30,44,75]},{\"tag\":\"mate\",\"ridge\":21,\"a\":5,\"owners\":[6,20,24,26,48,49,50,54,55,58]},{\"tag\":\"mate\",\"ridge\":21,\"a\":50,\"owners\":[5,24,25,26,53,54,55,56]},{\"tag\":\"mate\",\"ridge\":21,\"a\":53,\"owners\":[6,20,26,49,50,58]},{\"tag\":\"mate\",\"ridge\":21,\"a\":56,\"owners\":[6,20,24,48,49,50,55,58]},{\"tag\":\"mate\",\"ridge\":21,\"a\":58,\"owners\":[5,20,24,25,26,48,53,54,56]},{\"tag\":\"mate\",\"ridge\":81,\"a\":11,\"owners\":[5,25,34,42,53,57,61]},{\"tag\":\"mate\",\"ridge\":81,\"a\":25,\"owners\":[11,61,64,69]},{\"tag\":\"mate\",\"ridge\":81,\"a\":44,\"owners\":[5,53,57,61]},{\"tag\":\"mate\",\"ridge\":81,\"a\":53,\"owners\":[11,34,44,64]},{\"tag\":\"mate\",\"ridge\":81,\"a\":57,\"owners\":[11,34,42,44,61,64,69]},{\"tag\":\"mate\",\"ridge\":81,\"a\":64,\"owners\":[5,25,42,53,57]},{\"tag\":\"mate\",\"ridge\":84,\"a\":5,\"owners\":[17,73,75,88]},{\"tag\":\"mate\",\"ridge\":84,\"a\":25,\"owners\":[17,88]},{\"tag\":\"mate\",\"ridge\":84,\"a\":56,\"owners\":[17,73]},{\"tag\":\"mate\",\"ridge\":84,\"a\":57,\"owners\":[17,73,75,88]},{\"tag\":\"mate\",\"ridge\":84,\"a\":73,\"owners\":[5,56,57]},{\"tag\":\"mate\",\"ridge\":84,\"a\":88,\"owners\":[5,25,57]},{\"tag\":\"mate\",\"ridge\":517,\"a\":6,\"owners\":[7,23,32,52]},{\"tag\":\"mate\",\"ridge\":517,\"a\":7,\"owners\":[6,23,50,57]},{\"tag\":\"mate\",\"ridge\":517,\"a\":32,\"owners\":[6,50,57]},{\"tag\":\"mate\",\"ridge\":517,\"a\":50,\"owners\":[7,32]},{\"tag\":\"mate\",\"ridge\":517,\"a\":52,\"owners\":[6,57]},{\"tag\":\"mate\",\"ridge\":517,\"a\":57,\"owners\":[7,23,32,52]},{\"tag\":\"mate\",\"ridge\":529,\"a\":57,\"owners\":[9,65,66]},{\"tag\":\"mate\",\"ridge\":529,\"a\":58,\"owners\":[9,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":65,\"owners\":[6,57,58]},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[6,57]},{\"tag\":\"mate\",\"ridge\":532,\"a\":6,\"owners\":[85,86,89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":50,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[85,86,89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":58,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":85,\"owners\":[6,57,58]},{\"tag\":\"mate\",\"ridge\":532,\"a\":89,\"owners\":[6,50,57]},{\"tag\":\"mate\",\"ridge\":769,\"a\":7,\"owners\":[10,41,66]},{\"tag\":\"mate\",\"ridge\":769,\"a\":32,\"owners\":[10,66]},{\"tag\":\"mate\",\"ridge\":769,\"a\":41,\"owners\":[7,58]},{\"tag\":\"mate\",\"ridge\":769,\"a\":58,\"owners\":[10,41]},{\"tag\":\"mate\",\"ridge\":769,\"a\":66,\"owners\":[7,32]},{\"tag\":\"mate\",\"ridge\":772,\"a\":7,\"owners\":[72,86,87,89]},{\"tag\":\"mate\",\"ridge\":772,\"a\":32,\"owners\":[86,87,89]},{\"tag\":\"mate\",\"ridge\":772,\"a\":52,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":772,\"a\":58,\"owners\":[72,87]},{\"tag\":\"mate\",\"ridge\":772,\"a\":87,\"owners\":[7,32,58]},{\"tag\":\"mate\",\"ridge\":772,\"a\":89,\"owners\":[7,32,52,72]},{\"tag\":\"mate\",\"ridge\":25,\"a\":8,\"owners\":[9,20,33,34,48,49,50,61,63,66]},{\"tag\":\"mate\",\"ridge\":25,\"a\":50,\"owners\":[8,33,34,35,61,62,63,64]},{\"tag\":\"mate\",\"ridge\":25,\"a\":62,\"owners\":[9,20,34,49,50,66]},{\"tag\":\"mate\",\"ridge\":25,\"a\":64,\"owners\":[9,20,33,48,49,50,63,66]},{\"tag\":\"mate\",\"ridge\":25,\"a\":66,\"owners\":[8,20,33,34,35,48,61,62,64]},{\"tag\":\"mate\",\"ridge\":145,\"a\":8,\"owners\":[11,26,43,44,54,56,69]},{\"tag\":\"mate\",\"ridge\":145,\"a\":35,\"owners\":[11,54,56,69]},{\"tag\":\"mate\",\"ridge\":145,\"a\":62,\"owners\":[11,26,44,56]},{\"tag\":\"mate\",\"ridge\":145,\"a\":65,\"owners\":[11,26,43,44,54,56,69]},{\"tag\":\"mate\",\"ridge\":145,\"a\":69,\"owners\":[8,26,35,65]},{\"tag\":\"mate\",\"ridge\":152,\"a\":35,\"owners\":[18,90]},{\"tag\":\"mate\",\"ridge\":152,\"a\":64,\"owners\":[18,79]},{\"tag\":\"mate\",\"ridge\":152,\"a\":65,\"owners\":[18,79,80,90]},{\"tag\":\"mate\",\"ridge\":152,\"a\":79,\"owners\":[8,64,65]},{\"tag\":\"mate\",\"ridge\":152,\"a\":90,\"owners\":[8,35,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":41,\"owners\":[9,50,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":50,\"owners\":[10,41]},{\"tag\":\"mate\",\"ridge\":521,\"a\":52,\"owners\":[9,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":65,\"owners\":[10,23,41,52]},{\"tag\":\"mate\",\"ridge\":536,\"a\":9,\"owners\":[85,86,91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":50,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":65,\"owners\":[85,86,91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":66,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":536,\"a\":91,\"owners\":[9,50,65]},{\"tag\":\"mate\",\"ridge\":776,\"a\":10,\"owners\":[72,86,87,91]},{\"tag\":\"mate\",\"ridge\":776,\"a\":41,\"owners\":[86,87,91]},{\"tag\":\"mate\",\"ridge\":776,\"a\":52,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":776,\"a\":66,\"owners\":[72,87]},{\"tag\":\"mate\",\"ridge\":776,\"a\":86,\"owners\":[10,41]},{\"tag\":\"mate\",\"ridge\":776,\"a\":91,\"owners\":[10,41,52,72]},{\"tag\":\"mate\",\"ridge\":208,\"a\":56,\"owners\":[19,80,83,90]},{\"tag\":\"mate\",\"ridge\":208,\"a\":64,\"owners\":[19,75,83,88]},{\"tag\":\"mate\",\"ridge\":208,\"a\":83,\"owners\":[11,56,64]},{\"tag\":\"mate\",\"ridge\":208,\"a\":88,\"owners\":[11,44,64,80]},{\"tag\":\"mate\",\"ridge\":208,\"a\":90,\"owners\":[11,44,56,75]},{\"tag\":\"mate\",\"ridge\":38,\"a\":12,\"owners\":[13,21,24,28,29,70,71,74]},{\"tag\":\"mate\",\"ridge\":38,\"a\":13,\"owners\":[12,21,24,27,28,70,73,74,76]},{\"tag\":\"mate\",\"ridge\":38,\"a\":27,\"owners\":[13,70,71,74]},{\"tag\":\"mate\",\"ridge\":38,\"a\":29,\"owners\":[12,70,73,74,76]},{\"tag\":\"mate\",\"ridge\":38,\"a\":71,\"owners\":[12,24,27,28,73,74,76]},{\"tag\":\"mate\",\"ridge\":38,\"a\":73,\"owners\":[13,21,28,29,71]},{\"tag\":\"mate\",\"ridge\":38,\"a\":76,\"owners\":[13,21,24,29,70,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":27,\"owners\":[16,78,81,83]},{\"tag\":\"mate\",\"ridge\":98,\"a\":45,\"owners\":[12,73,77,78]},{\"tag\":\"mate\",\"ridge\":98,\"a\":73,\"owners\":[16,36,45,46,81]},{\"tag\":\"mate\",\"ridge\":98,\"a\":77,\"owners\":[16,36,42,45,78,81,83]},{\"tag\":\"mate\",\"ridge\":98,\"a\":81,\"owners\":[12,27,42,46,73,77]},{\"tag\":\"mate\",\"ridge\":98,\"a\":83,\"owners\":[12,27,36,46,77]},{\"tag\":\"mate\",\"ridge\":100,\"a\":17,\"owners\":[12,27,59,60,76,77]},{\"tag\":\"mate\",\"ridge\":100,\"a\":27,\"owners\":[17,88]},{\"tag\":\"mate\",\"ridge\":100,\"a\":53,\"owners\":[12,76,77]},{\"tag\":\"mate\",\"ridge\":100,\"a\":76,\"owners\":[17,53,60]},{\"tag\":\"mate\",\"ridge\":100,\"a\":77,\"owners\":[17,53,59,88]},{\"tag\":\"mate\",\"ridge\":100,\"a\":88,\"owners\":[12,27,60,77]},{\"tag\":\"mate\",\"ridge\":290,\"a\":13,\"owners\":[15,38,46,47,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":15,\"owners\":[13,29,46,47,77]},{\"tag\":\"mate\",\"ridge\":290,\"a\":29,\"owners\":[15,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":38,\"owners\":[13,77]},{\"tag\":\"mate\",\"ridge\":290,\"a\":77,\"owners\":[15,38,47,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":82,\"owners\":[13,29,46,77]},{\"tag\":\"mate\",\"ridge\":292,\"a\":29,\"owners\":[84,87,89]},{\"tag\":\"mate\",\"ridge\":292,\"a\":71,\"owners\":[55,60,89]},{\"tag\":\"mate\",\"ridge\":292,\"a\":77,\"owners\":[51,55,84,87,89]},{\"tag\":\"mate\",\"ridge\":292,\"a\":87,\"owners\":[13,29,55,60,77]},{\"tag\":\"mate\",\"ridge\":42,\"a\":14,\"owners\":[15,21,33,36,38,70,71,78]},{\"tag\":\"mate\",\"ridge\":42,\"a\":15,\"owners\":[14,21,33,36,37,70,78,79,81]},{\"tag\":\"mate\",\"ridge\":42,\"a\":37,\"owners\":[15,70,71,78]},{\"tag\":\"mate\",\"ridge\":42,\"a\":38,\"owners\":[14,70,78,79,81]},{\"tag\":\"mate\",\"ridge\":42,\"a\":71,\"owners\":[14,33,36,37,78,79,81]},{\"tag\":\"mate\",\"ridge\":42,\"a\":79,\"owners\":[15,21,36,38,71]},{\"tag\":\"mate\",\"ridge\":42,\"a\":81,\"owners\":[15,21,33,38,70,71]},{\"tag\":\"mate\",\"ridge\":162,\"a\":37,\"owners\":[16,74,76,83]},{\"tag\":\"mate\",\"ridge\":162,\"a\":45,\"owners\":[14,74,79,82]},{\"tag\":\"mate\",\"ridge\":162,\"a\":79,\"owners\":[16,28,45,47,76]},{\"tag\":\"mate\",\"ridge\":162,\"a\":82,\"owners\":[16,28,43,45,74,76,83]},{\"tag\":\"mate\",\"ridge\":162,\"a\":83,\"owners\":[14,28,37,47,82]},{\"tag\":\"mate\",\"ridge\":168,\"a\":18,\"owners\":[14,37,67,68,81,82]},{\"tag\":\"mate\",\"ridge\":168,\"a\":37,\"owners\":[18,90]},{\"tag\":\"mate\",\"ridge\":168,\"a\":62,\"owners\":[14,81,82]},{\"tag\":\"mate\",\"ridge\":168,\"a\":81,\"owners\":[18,62,68]},{\"tag\":\"mate\",\"ridge\":168,\"a\":82,\"owners\":[18,62,67,90]},{\"tag\":\"mate\",\"ridge\":168,\"a\":90,\"owners\":[14,37,68,82]},{\"tag\":\"mate\",\"ridge\":296,\"a\":15,\"owners\":[51,63,68,84,87,91]},{\"tag\":\"mate\",\"ridge\":296,\"a\":71,\"owners\":[63,68,91]},{\"tag\":\"mate\",\"ridge\":296,\"a\":82,\"owners\":[51,63,84,87,91]},{\"tag\":\"mate\",\"ridge\":296,\"a\":87,\"owners\":[15,38,63,68,82]},{\"tag\":\"mate\",\"ridge\":224,\"a\":16,\"owners\":[19,59,67,69,88,90]},{\"tag\":\"mate\",\"ridge\":224,\"a\":45,\"owners\":[19,88,90]},{\"tag\":\"mate\",\"ridge\":224,\"a\":69,\"owners\":[16,76,81]},{\"tag\":\"mate\",\"ridge\":224,\"a\":76,\"owners\":[19,67,69,90]},{\"tag\":\"mate\",\"ridge\":224,\"a\":81,\"owners\":[19,59,69,88]},{\"tag\":\"mate\",\"ridge\":224,\"a\":88,\"owners\":[16,45,67,81]},{\"tag\":\"mate\",\"ridge\":224,\"a\":90,\"owners\":[16,45,59,76]},{\"tag\":\"mate\",\"ridge\":52,\"a\":17,\"owners\":[24,48,54,55,70,74,84,85,89]},{\"tag\":\"mate\",\"ridge\":52,\"a\":53,\"owners\":[70,74,84,85,89]},{\"tag\":\"mate\",\"ridge\":52,\"a\":73,\"owners\":[48,54,55,84,85,89]},{\"tag\":\"mate\",\"ridge\":52,\"a\":85,\"owners\":[17,24,53,54,55,73,74,88]},{\"tag\":\"mate\",\"ridge\":52,\"a\":88,\"owners\":[24,48,55,70,84,85,89]},{\"tag\":\"mate\",\"ridge\":52,\"a\":89,\"owners\":[17,24,48,53,54,70,73,74,88]},{\"tag\":\"three\",\"ridge\":52,\"vertices\":[48,88,89]},{\"tag\":\"three\",\"ridge\":52,\"vertices\":[70,88,89]},{\"tag\":\"mate\",\"ridge\":112,\"a\":53,\"owners\":[19,78,83,90]},{\"tag\":\"mate\",\"ridge\":112,\"a\":69,\"owners\":[17,73,78]},{\"tag\":\"mate\",\"ridge\":112,\"a\":73,\"owners\":[19,61,69,90]},{\"tag\":\"mate\",\"ridge\":112,\"a\":83,\"owners\":[17,53,61]},{\"tag\":\"mate\",\"ridge\":112,\"a\":90,\"owners\":[17,42,53,73]},{\"tag\":\"mate\",\"ridge\":56,\"a\":79,\"owners\":[48,61,63,84,85,91]},{\"tag\":\"mate\",\"ridge\":56,\"a\":85,\"owners\":[18,33,61,62,63,78,79,90]},{\"tag\":\"mate\",\"ridge\":56,\"a\":91,\"owners\":[18,33,48,61,62,70,78,79,90]},{\"tag\":\"mate\",\"ridge\":176,\"a\":62,\"owners\":[19,74,83,88]},{\"tag\":\"mate\",\"ridge\":176,\"a\":69,\"owners\":[18,74,79]},{\"tag\":\"mate\",\"ridge\":176,\"a\":79,\"owners\":[19,54,69,88]},{\"tag\":\"mate\",\"ridge\":176,\"a\":83,\"owners\":[18,54,62]},{\"tag\":\"mate\",\"ridge\":176,\"a\":88,\"owners\":[18,43,62,79]},{\"tag\":\"mate\",\"ridge\":30,\"a\":20,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":30,\"a\":70,\"owners\":[20]},{\"tag\":\"mate\",\"ridge\":45,\"a\":21,\"owners\":[48,51]},{\"tag\":\"mate\",\"ridge\":45,\"a\":48,\"owners\":[21,51]},{\"tag\":\"mate\",\"ridge\":45,\"a\":51,\"owners\":[21,48]},{\"tag\":\"mate\",\"ridge\":526,\"a\":23,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":526,\"a\":72,\"owners\":[23]},{\"tag\":\"mate\",\"ridge\":51,\"a\":24,\"owners\":[33,42,43]},{\"tag\":\"mate\",\"ridge\":51,\"a\":33,\"owners\":[24,42,43]},{\"tag\":\"mate\",\"ridge\":51,\"a\":42,\"owners\":[24,33,43]},{\"tag\":\"mate\",\"ridge\":51,\"a\":43,\"owners\":[24,33,42]},{\"tag\":\"mate\",\"ridge\":150,\"a\":26,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":150,\"a\":74,\"owners\":[26,75]},{\"tag\":\"mate\",\"ridge\":150,\"a\":75,\"owners\":[26,74]},{\"tag\":\"mate\",\"ridge\":165,\"a\":28,\"owners\":[54,59]},{\"tag\":\"mate\",\"ridge\":165,\"a\":54,\"owners\":[28,59]},{\"tag\":\"mate\",\"ridge\":165,\"a\":59,\"owners\":[28,54]},{\"tag\":\"mate\",\"ridge\":90,\"a\":34,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":90,\"a\":78,\"owners\":[34,80]},{\"tag\":\"mate\",\"ridge\":90,\"a\":80,\"owners\":[34,78]},{\"tag\":\"mate\",\"ridge\":105,\"a\":36,\"owners\":[61,67]},{\"tag\":\"mate\",\"ridge\":105,\"a\":61,\"owners\":[36,67]},{\"tag\":\"mate\",\"ridge\":105,\"a\":67,\"owners\":[36,61]},{\"tag\":\"mate\",\"ridge\":353,\"a\":46,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":353,\"a\":60,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":417,\"a\":47,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":417,\"a\":68,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":284,\"a\":86,\"owners\":[49,84]},{\"tag\":\"mate\",\"ridge\":305,\"a\":55,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":305,\"a\":63,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":556,\"a\":85,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":556,\"a\":87,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":816,\"a\":89,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":816,\"a\":91,\"owners\":[89]},{\"tag\":\"group_or\",\"kind\":1,\"index\":0,\"members\":[0],\"full_literals\":[-93,1]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,93]},{\"tag\":\"group_or\",\"kind\":1,\"index\":1,\"members\":[1],\"full_literals\":[-94,2]},{\"tag\":\"group_take\",\"kind\":1,\"index\":1,\"member\":1,\"full_literals\":[-2,94]},{\"tag\":\"group_or\",\"kind\":1,\"index\":2,\"members\":[2],\"full_literals\":[-95,3]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-3,95]},{\"tag\":\"group_or\",\"kind\":1,\"index\":3,\"members\":[3],\"full_literals\":[-96,4]},{\"tag\":\"group_take\",\"kind\":1,\"index\":3,\"member\":3,\"full_literals\":[-4,96]},{\"tag\":\"group_or\",\"kind\":1,\"index\":4,\"members\":[4],\"full_literals\":[-97,5]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-5,97]},{\"tag\":\"group_or\",\"kind\":1,\"index\":5,\"members\":[5],\"full_literals\":[-98,6]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-6,98]},{\"tag\":\"group_or\",\"kind\":1,\"index\":6,\"members\":[6],\"full_literals\":[-99,7]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-7,99]},{\"tag\":\"group_or\",\"kind\":1,\"index\":7,\"members\":[7],\"full_literals\":[-100,8]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-8,100]},{\"tag\":\"group_or\",\"kind\":1,\"index\":8,\"members\":[8],\"full_literals\":[-101,9]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-9,101]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-10,102]},{\"tag\":\"group_or\",\"kind\":1,\"index\":10,\"members\":[10],\"full_literals\":[-103,11]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-11,103]},{\"tag\":\"group_or\",\"kind\":1,\"index\":11,\"members\":[11],\"full_literals\":[-104,12]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-12,104]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-13,105]},{\"tag\":\"group_or\",\"kind\":1,\"index\":13,\"members\":[13],\"full_literals\":[-106,14]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-14,106]},{\"tag\":\"group_or\",\"kind\":1,\"index\":14,\"members\":[14],\"full_literals\":[-107,15]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-15,107]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-16,108]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-17,109]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-18,110]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-19,111]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-20,112]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-113,93,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-94,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-115,96,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-96,-97,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-117,95,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-115,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-95,-115,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-95,-116,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-120,113,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-117,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-118,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-119,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-113,false,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-113,-117,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-113,-118,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-113,-119,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-114,false,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-114,-117,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-114,-118,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-124,98,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-99,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-98,-99,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-102,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-127,101,false],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-101,false,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-101,-102,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-126,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-129,100,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-127,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-100,-126,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-100,-127,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-128,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-132,124,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-129,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-130,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-124,false,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-124,-128,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-125,false,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-125,-128,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-131,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-135,120,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-132,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-120,false,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-120,-131,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-120,-132,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-120,-133,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-121,false,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-121,-131,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-121,-132,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-122,false,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-122,-131,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-122,-132,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":4,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-123,false,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":4,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-123,-131,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-139,103,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-104,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-103,false,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-103,-104,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-141,106,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-107,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-106,false,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-106,-107,142],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-141,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-142,144],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-144,false,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-105,-141,144],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-143,145],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-146,139,144],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-144,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-139,false,145],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-139,-143,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-139,-144,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-140,false,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-140,-143,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-109,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-108,false,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-108,-109,149],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-112,150],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-111,false,150],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-111,-112,151],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-150,152],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-151,153],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,152],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-150,153],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-110,-151,154],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-152,155],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-153,156],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-154,157],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-148,false,155],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-148,-152,156],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-148,-153,157],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-149,false,156],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-149,-152,157],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-155,158],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-156,159],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-157,160],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-145,false,158],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-145,-155,159],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-145,-156,160],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-145,-157,161],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-146,false,159],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-146,-155,160],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-146,-156,161],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-146,-157,162],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-147,-155,161],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-147,-156,162],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":5,\"direction\":\"forward\",\"full_literals\":[false,-162,163],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-134,-161,163],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-135,-160,163],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-136,-159,163],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":4,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-137,-158,163],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":5,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-138,false,163],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[50,57,58],\"full_literals\":[-164,51,58,59]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":50,\"full_literals\":[-51,164]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":57,\"full_literals\":[-58,164]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":58,\"full_literals\":[-59,164]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[65,66],\"full_literals\":[-165,66,67]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":65,\"full_literals\":[-66,165]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":66,\"full_literals\":[-67,165]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[22,32,41,52],\"full_literals\":[-166,23,33,42,53]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":32,\"full_literals\":[-33,166]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":41,\"full_literals\":[-42,166]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":52,\"full_literals\":[-53,166]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[27,29,31,77],\"full_literals\":[-167,28,30,32,78]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":27,\"full_literals\":[-28,167]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":29,\"full_literals\":[-30,167]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":31,\"full_literals\":[-32,167]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":77,\"full_literals\":[-78,167]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[38,71,82],\"full_literals\":[-168,39,72,83]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":38,\"full_literals\":[-39,168]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":71,\"full_literals\":[-72,168]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":82,\"full_literals\":[-83,168]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[30,56,76,88],\"full_literals\":[-169,31,57,77,89]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":30,\"full_literals\":[-31,169]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":56,\"full_literals\":[-57,169]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":76,\"full_literals\":[-77,169]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":88,\"full_literals\":[-89,169]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[35,37,39,40],\"full_literals\":[-170,36,38,40,41]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":35,\"full_literals\":[-36,170]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":37,\"full_literals\":[-38,170]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":39,\"full_literals\":[-40,170]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":40,\"full_literals\":[-41,170]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[45,53,62,69],\"full_literals\":[-171,46,54,63,70]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":45,\"full_literals\":[-46,171]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":53,\"full_literals\":[-54,171]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":62,\"full_literals\":[-63,171]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":69,\"full_literals\":[-70,171]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[25,44,73,79,83],\"full_literals\":[-172,26,45,74,80,84]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":44,\"full_literals\":[-45,172]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":73,\"full_literals\":[-74,172]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":79,\"full_literals\":[-80,172]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[64,81,90],\"full_literals\":[-173,65,82,91]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":64,\"full_literals\":[-65,173]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":81,\"full_literals\":[-82,173]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":90,\"full_literals\":[-91,173]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-174,164,165],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-175,164,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-175,false,165],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-164,-165,175],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-176,167,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-168,176],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-177,167,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-167,false,176],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-177,false,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-167,-168,177],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-178,166,176],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-179,166,177],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-180,166,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-179,false,176],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-166,-176,179],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-180,false,177],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-166,-177,180],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-181,174,180],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-182,174,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-181,175,179],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-182,175,180],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-183,175,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-181,false,178],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-182,false,179],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-175,-179,182],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-183,false,180],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-175,-180,183],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-184,169,170],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-185,169,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-169,false,184],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-185,false,170],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-169,-170,185],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-186,172,173],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-173,186],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-187,172,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-172,false,186],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-187,false,173],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-172,-173,187],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-188,171,186],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-189,171,187],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-187,189],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-190,171,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-189,false,186],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-171,-186,189],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-190,false,187],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-171,-187,190],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-191,184,190],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-192,184,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-191,185,189],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-192,185,190],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-184,-190,192],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-193,185,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-191,false,188],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-192,false,189],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-185,-189,192],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-193,false,190],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-185,-190,193],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-194,181,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-194,182,193],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-194,183,192],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"forward\",\"full_literals\":[-182,-193,195],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-194,false,191],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-183,-192,195],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-50,196]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":85,\"full_literals\":[-86,196]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":89,\"full_literals\":[-90,196]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-85,197]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-88,197]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":91,\"full_literals\":[-92,197]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[20,21,23,86],\"full_literals\":[-198,21,22,24,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":20,\"full_literals\":[-21,198]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":21,\"full_literals\":[-22,198]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":23,\"full_literals\":[-24,198]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-87,198]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[48,70,72],\"full_literals\":[-199,49,71,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":48,\"full_literals\":[-49,199]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-71,199]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-73,199]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[24,26,34],\"full_literals\":[-200,25,27,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":24,\"full_literals\":[-25,200]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":26,\"full_literals\":[-27,200]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":34,\"full_literals\":[-35,200]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[33,74,78],\"full_literals\":[-201,34,75,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":33,\"full_literals\":[-34,201]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-75,201]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-79,201]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[42,75,80],\"full_literals\":[-202,43,76,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":42,\"full_literals\":[-43,202]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-76,202]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-81,202]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[28,36,43,46,47,51,55],\"full_literals\":[-203,29,37,44,47,48,52,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":28,\"full_literals\":[-29,203]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":36,\"full_literals\":[-37,203]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":43,\"full_literals\":[-44,203]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":46,\"full_literals\":[-47,203]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":47,\"full_literals\":[-48,203]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":51,\"full_literals\":[-52,203]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":55,\"full_literals\":[-56,203]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[54,60,61,63,68],\"full_literals\":[-204,55,61,62,64,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":54,\"full_literals\":[-55,204]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":60,\"full_literals\":[-61,204]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":61,\"full_literals\":[-62,204]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":63,\"full_literals\":[-64,204]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":68,\"full_literals\":[-69,204]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[59,67],\"full_literals\":[-205,60,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":59,\"full_literals\":[-60,205]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":67,\"full_literals\":[-68,205]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0059\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-197,206],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0059\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-196,false,206],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0059\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-196,-197,207],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0067\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-208,199,200],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0067\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-200,208],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0067\",\"joined_name\":\"grouped3_0066\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-199,false,208],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0064\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-209,198,208],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0064\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-208,209],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0064\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-198,false,209],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0059\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0060\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-209,210],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0059\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0060\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-206,false,210],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0059\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0060\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-206,-209,211],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0059\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0060\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-207,-209,212],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0069\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-213,201,202],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0069\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-202,213],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0069\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-201,false,213],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0069\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-201,-202,214],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-215,204,205],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-205,215],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-204,false,215],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-204,-205,216],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-217,203,215],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-216,218],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-203,false,217],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-203,-215,218],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-219,213,217],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-217,219],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-218,220],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-213,false,219],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-213,-217,220],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-214,false,220],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-210,-220,221],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-211,-219,221],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-212,false,221],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[0,9,10,15,32,40,45,57,64,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[0,9,10,15,32,40,44,57,62,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[0,9,10,15,32,40,45,57,64,77,79,84,86,88]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[0,9,10,15,32,40,44,57,62,77,81,84,86,88]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[5,6,10,18,27,32,40,44,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[5,6,10,18,30,32,40,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[5,6,7,17,31,39,41,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[6,7,11,19,31,39,41,53,65,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[5,6,7,17,31,37,41,44,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[0,6,10,14,32,40,44,53,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[0,1,9,15,40,44,52,57,62,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[0,9,10,15,32,40,44,57,62,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[6,13,14,15,31,40,44,52,53,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[0,9,10,12,32,40,44,57,62,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[6,7,10,14,31,40,44,53,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[0,6,10,14,32,40,45,56,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[0,1,9,15,40,45,52,57,64,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[0,9,10,15,32,40,45,57,64,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[6,13,14,15,31,40,45,52,56,65,73,89,90,91]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[0,9,10,12,32,40,45,57,64,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[6,7,10,14,31,40,45,56,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[4,6,7,16,31,37,41,56,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[6,15,16,19,30,32,40,53,64,66,77,79,85,87]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[6,14,15,18,30,32,40,53,64,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[6,14,15,18,25,32,40,45,64,66,77,85,87,88]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[0,5,6,15,32,40,45,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[4,6,11,15,25,32,40,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[0,5,6,15,32,40,44,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[1,9,11,16,30,35,41,53,58,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[0,3,6,17,32,39,56,62,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[0,1,9,17,35,41,45,56,58,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[0,1,9,17,39,41,56,58,62,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":32,\"vertices\":[0,3,6,17,32,35,45,56,66,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":33,\"vertices\":[1,9,11,16,25,39,41,58,62,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":34,\"vertices\":[7,12,13,17,31,35,41,45,50,56,82,89,90,91]},{\"tag\":\"block\",\"leaf\":35,\"vertices\":[0,5,10,15,32,40,45,50,64,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":36,\"vertices\":[7,13,16,19,31,39,41,50,56,62,73,82,89,91]},{\"tag\":\"block\",\"leaf\":37,\"vertices\":[7,12,13,17,31,39,41,50,56,62,82,83,89,91]},{\"tag\":\"block\",\"leaf\":38,\"vertices\":[4,7,11,13,31,35,41,50,53,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":39,\"vertices\":[0,5,10,15,32,40,44,50,62,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":40,\"vertices\":[1,7,11,16,30,35,41,50,53,77,82,89,90,91]},{\"tag\":\"block\",\"leaf\":41,\"vertices\":[0,3,10,17,32,39,50,56,62,77,82,83,89,91]},{\"tag\":\"block\",\"leaf\":42,\"vertices\":[0,1,7,17,35,41,45,50,56,77,82,89,90,91]},{\"tag\":\"block\",\"leaf\":43,\"vertices\":[0,1,7,17,39,41,50,56,62,77,82,83,89,91]},{\"tag\":\"block\",\"leaf\":44,\"vertices\":[0,3,10,17,32,35,45,50,56,77,82,89,90,91]},{\"tag\":\"block\",\"leaf\":45,\"vertices\":[1,7,11,16,25,39,41,50,62,77,82,88,89,91]},{\"tag\":\"block\",\"leaf\":46,\"vertices\":[7,13,15,17,31,37,41,44,57,65,76,85,87,90]},{\"tag\":\"block\",\"leaf\":47,\"vertices\":[7,13,15,17,31,39,41,57,65,69,76,79,85,87]},{\"tag\":\"block\",\"leaf\":48,\"vertices\":[0,10,15,18,32,40,44,57,65,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":49,\"vertices\":[0,2,7,17,29,41,44,57,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":50,\"vertices\":[0,10,11,15,32,40,45,57,65,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":51,\"vertices\":[0,10,11,16,32,38,39,57,65,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":52,\"vertices\":[7,13,17,18,31,39,41,57,65,69,76,82,85,87]},{\"tag\":\"block\",\"leaf\":53,\"vertices\":[7,13,16,18,31,39,41,57,65,69,73,82,85,87]},{\"tag\":\"block\",\"leaf\":54,\"vertices\":[7,13,15,17,31,37,41,44,57,65,76,84,86,90]},{\"tag\":\"block\",\"leaf\":55,\"vertices\":[7,13,15,17,31,39,41,57,65,69,76,79,84,86]},{\"tag\":\"block\",\"leaf\":56,\"vertices\":[0,10,15,18,32,40,44,57,65,77,81,84,86,88]},{\"tag\":\"block\",\"leaf\":57,\"vertices\":[0,2,7,17,29,41,44,57,65,76,82,84,86,90]},{\"tag\":\"block\",\"leaf\":58,\"vertices\":[0,10,11,15,32,40,45,57,65,77,79,84,86,88]},{\"tag\":\"block\",\"leaf\":59,\"vertices\":[0,10,11,16,32,38,39,57,65,77,79,84,86,88]},{\"tag\":\"block\",\"leaf\":60,\"vertices\":[7,13,17,18,31,39,41,57,65,69,76,82,84,86]},{\"tag\":\"block\",\"leaf\":61,\"vertices\":[7,13,16,18,31,39,41,57,65,69,73,82,84,86]},{\"tag\":\"block\",\"leaf\":62,\"vertices\":[7,17,18,19,31,37,41,44,57,65,71,76,89,91]},{\"tag\":\"block\",\"leaf\":63,\"vertices\":[7,14,17,18,31,39,41,57,65,69,71,76,89,91]},{\"tag\":\"block\",\"leaf\":64,\"vertices\":[1,15,17,18,30,40,52,57,65,69,77,81,89,91]},{\"tag\":\"block\",\"leaf\":65,\"vertices\":[7,13,17,18,31,39,41,57,65,69,76,82,89,91]},{\"tag\":\"block\",\"leaf\":66,\"vertices\":[11,13,17,19,31,38,39,52,57,65,76,79,89,91]},{\"tag\":\"block\",\"leaf\":67,\"vertices\":[7,11,17,19,31,39,41,57,65,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":68,\"vertices\":[1,15,16,17,30,40,52,57,65,69,77,79,89,91]},{\"tag\":\"block\",\"leaf\":69,\"vertices\":[7,13,16,18,31,39,41,57,65,69,73,82,89,91]},{\"tag\":\"block\",\"leaf\":70,\"vertices\":[4,13,15,17,31,40,52,57,65,69,76,79,89,91]},{\"tag\":\"block\",\"leaf\":71,\"vertices\":[1,13,15,18,30,40,52,57,65,69,73,81,89,91]},{\"tag\":\"block\",\"leaf\":72,\"vertices\":[7,13,15,17,31,39,41,57,65,69,76,79,89,91]},{\"tag\":\"block\",\"leaf\":73,\"vertices\":[7,12,16,17,31,39,41,57,65,69,71,79,89,91]},{\"tag\":\"block\",\"leaf\":74,\"vertices\":[7,14,16,18,31,39,41,57,65,69,71,73,89,91]},{\"tag\":\"block\",\"leaf\":75,\"vertices\":[0,1,7,17,39,41,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":76,\"vertices\":[0,4,10,17,32,40,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":77,\"vertices\":[0,3,10,17,32,39,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":78,\"vertices\":[0,4,10,18,32,40,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":79,\"vertices\":[4,7,10,17,31,40,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":80,\"vertices\":[1,7,10,18,30,40,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":81,\"vertices\":[4,7,11,17,31,37,41,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":82,\"vertices\":[7,12,16,18,31,37,41,44,57,65,71,88,89,91]},{\"tag\":\"block\",\"leaf\":83,\"vertices\":[7,12,16,17,31,37,41,44,57,65,71,89,90,91]},{\"tag\":\"block\",\"leaf\":84,\"vertices\":[0,1,2,18,38,44,52,57,65,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":85,\"vertices\":[0,2,7,17,29,41,44,57,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":86,\"vertices\":[0,14,15,17,29,40,44,52,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":87,\"vertices\":[0,1,7,17,37,41,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":88,\"vertices\":[0,10,14,17,32,40,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":89,\"vertices\":[0,3,10,17,32,37,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":90,\"vertices\":[0,10,15,18,32,40,44,57,65,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":91,\"vertices\":[7,13,15,17,31,37,41,44,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":92,\"vertices\":[0,1,15,18,40,44,52,57,65,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":93,\"vertices\":[0,12,15,18,29,40,44,52,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":94,\"vertices\":[1,13,15,18,27,40,44,52,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":95,\"vertices\":[12,13,15,18,31,40,44,52,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":96,\"vertices\":[0,10,12,18,32,40,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":97,\"vertices\":[7,10,12,18,31,40,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":98,\"vertices\":[1,7,10,18,27,40,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":99,\"vertices\":[4,7,11,16,31,37,41,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":100,\"vertices\":[0,1,11,16,38,39,52,57,65,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":101,\"vertices\":[0,10,11,16,32,38,39,57,65,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":102,\"vertices\":[11,12,13,16,31,38,39,52,57,65,79,88,89,91]},{\"tag\":\"block\",\"leaf\":103,\"vertices\":[1,7,11,16,30,37,41,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":104,\"vertices\":[7,11,12,16,31,39,41,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":105,\"vertices\":[1,7,11,16,27,39,41,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":106,\"vertices\":[0,1,11,15,40,45,52,57,65,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":107,\"vertices\":[0,10,11,15,32,40,45,57,65,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":108,\"vertices\":[11,12,13,15,31,40,45,52,57,65,79,88,89,91]},{\"tag\":\"block\",\"leaf\":109,\"vertices\":[0,10,11,12,32,40,45,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":110,\"vertices\":[0,10,11,14,32,40,45,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":111,\"vertices\":[7,10,11,12,31,40,45,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":112,\"vertices\":[7,12,13,15,31,40,45,57,64,66,79,85,87,88]},{\"tag\":\"block\",\"leaf\":113,\"vertices\":[7,12,13,15,31,40,44,57,62,66,81,85,87,88]},{\"tag\":\"block\",\"leaf\":114,\"vertices\":[0,1,7,15,40,45,57,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":115,\"vertices\":[0,1,7,15,40,44,57,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":116,\"vertices\":[4,13,15,16,27,32,40,57,64,66,79,85,87,88]},{\"tag\":\"block\",\"leaf\":117,\"vertices\":[0,12,13,15,32,40,45,57,64,66,79,85,87,88]},{\"tag\":\"block\",\"leaf\":118,\"vertices\":[5,13,15,17,31,37,41,44,58,65,76,85,87,90]},{\"tag\":\"block\",\"leaf\":119,\"vertices\":[0,12,13,15,32,40,44,57,62,66,81,85,87,88]},{\"tag\":\"block\",\"leaf\":120,\"vertices\":[11,13,15,19,30,32,40,57,62,66,73,81,85,87]},{\"tag\":\"block\",\"leaf\":121,\"vertices\":[5,13,15,17,31,39,41,58,65,69,76,79,85,87]},{\"tag\":\"block\",\"leaf\":122,\"vertices\":[0,15,17,19,32,40,45,57,64,66,77,79,85,87]},{\"tag\":\"block\",\"leaf\":123,\"vertices\":[0,15,17,19,32,40,44,57,62,66,77,81,85,87]},{\"tag\":\"block\",\"leaf\":124,\"vertices\":[0,3,11,17,32,35,45,57,66,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":125,\"vertices\":[0,3,11,17,32,39,57,62,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":126,\"vertices\":[0,8,15,18,32,40,44,57,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":127,\"vertices\":[0,2,5,17,29,41,44,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":128,\"vertices\":[0,3,11,18,32,35,45,57,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":129,\"vertices\":[0,4,11,18,32,35,38,57,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":130,\"vertices\":[0,14,15,18,32,40,45,57,64,66,77,85,87,88]},{\"tag\":\"block\",\"leaf\":131,\"vertices\":[0,1,2,17,41,45,56,58,65,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":132,\"vertices\":[0,3,11,16,32,39,57,62,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":133,\"vertices\":[0,4,11,15,32,40,57,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":134,\"vertices\":[0,14,15,16,32,40,44,57,62,66,77,85,87,88]},{\"tag\":\"block\",\"leaf\":135,\"vertices\":[0,1,2,16,41,44,53,58,65,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":136,\"vertices\":[0,1,2,13,41,44,53,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":137,\"vertices\":[0,8,11,15,32,40,45,57,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":138,\"vertices\":[0,8,11,16,32,38,39,57,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":139,\"vertices\":[0,4,15,16,32,40,57,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":140,\"vertices\":[0,1,2,13,41,45,56,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":141,\"vertices\":[0,2,4,16,29,41,56,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":142,\"vertices\":[1,11,16,18,25,39,41,58,65,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":143,\"vertices\":[11,17,18,19,25,29,39,41,58,65,76,82,85,87]},{\"tag\":\"block\",\"leaf\":144,\"vertices\":[11,12,16,18,25,29,39,41,58,65,82,85,87,88]},{\"tag\":\"block\",\"leaf\":145,\"vertices\":[11,13,18,19,31,39,41,53,58,65,76,82,85,87]},{\"tag\":\"block\",\"leaf\":146,\"vertices\":[11,12,13,18,31,39,41,53,58,65,82,83,85,87]},{\"tag\":\"block\",\"leaf\":147,\"vertices\":[0,1,11,18,39,41,53,58,65,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":148,\"vertices\":[0,1,17,18,39,41,56,58,65,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":149,\"vertices\":[0,12,17,18,29,39,41,56,58,65,82,83,85,87]},{\"tag\":\"block\",\"leaf\":150,\"vertices\":[1,13,17,18,27,39,41,56,58,65,82,83,85,87]},{\"tag\":\"block\",\"leaf\":151,\"vertices\":[12,13,17,18,31,39,41,56,58,65,82,83,85,87]},{\"tag\":\"block\",\"leaf\":152,\"vertices\":[13,16,18,19,31,39,41,56,58,65,73,82,85,87]},{\"tag\":\"block\",\"leaf\":153,\"vertices\":[0,16,18,19,29,39,41,56,58,65,73,82,85,87]},{\"tag\":\"block\",\"leaf\":154,\"vertices\":[5,13,17,18,31,39,41,58,65,69,76,82,85,87]},{\"tag\":\"block\",\"leaf\":155,\"vertices\":[5,13,16,18,31,39,41,58,65,69,73,82,85,87]},{\"tag\":\"block\",\"leaf\":156,\"vertices\":[1,16,17,18,25,39,41,58,65,69,77,82,85,87]},{\"tag\":\"block\",\"leaf\":157,\"vertices\":[1,13,17,18,25,39,41,58,65,69,76,82,85,87]},{\"tag\":\"block\",\"leaf\":158,\"vertices\":[2,6,7,13,31,41,45,56,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":159,\"vertices\":[2,6,7,13,31,41,44,53,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":160,\"vertices\":[2,6,7,13,31,41,45,56,65,73,82,84,86,90]},{\"tag\":\"block\",\"leaf\":161,\"vertices\":[2,6,7,13,31,41,44,53,65,76,82,84,86,90]},{\"tag\":\"block\",\"leaf\":162,\"vertices\":[7,8,9,17,31,37,41,44,57,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":163,\"vertices\":[7,8,9,17,31,39,41,57,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":164,\"vertices\":[8,9,10,18,30,32,40,57,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":165,\"vertices\":[9,10,11,19,30,32,40,57,62,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":166,\"vertices\":[8,9,10,18,27,32,40,44,57,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":167,\"vertices\":[2,7,9,12,31,41,44,57,62,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":168,\"vertices\":[2,3,6,13,31,44,52,53,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":169,\"vertices\":[2,6,7,13,31,41,44,53,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":170,\"vertices\":[9,12,13,15,31,40,44,52,57,62,81,88,89,91]},{\"tag\":\"block\",\"leaf\":171,\"vertices\":[2,6,7,14,31,41,44,53,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":172,\"vertices\":[7,9,10,12,31,40,44,57,62,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":173,\"vertices\":[2,7,9,12,31,41,45,57,64,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":174,\"vertices\":[2,3,6,13,31,45,52,56,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":175,\"vertices\":[2,6,7,13,31,41,45,56,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":176,\"vertices\":[9,12,13,15,31,40,45,52,57,64,79,88,89,91]},{\"tag\":\"block\",\"leaf\":177,\"vertices\":[2,6,7,14,31,41,45,56,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":178,\"vertices\":[7,9,10,12,31,40,45,57,64,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":179,\"vertices\":[4,9,10,16,27,32,40,57,64,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":180,\"vertices\":[9,13,16,19,31,39,41,56,58,62,73,82,85,87]},{\"tag\":\"block\",\"leaf\":181,\"vertices\":[9,12,13,17,31,39,41,56,58,62,82,83,85,87]},{\"tag\":\"block\",\"leaf\":182,\"vertices\":[9,12,13,17,31,35,41,45,56,58,82,85,87,90]},{\"tag\":\"block\",\"leaf\":183,\"vertices\":[2,8,9,13,31,41,45,56,58,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":184,\"vertices\":[4,9,11,13,31,35,41,53,58,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":185,\"vertices\":[2,8,9,13,31,41,44,53,58,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":186,\"vertices\":[3,6,11,16,25,32,39,62,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":187,\"vertices\":[1,2,9,18,30,41,53,58,64,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":188,\"vertices\":[2,3,6,18,25,32,45,64,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":189,\"vertices\":[2,3,6,18,30,32,53,64,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":190,\"vertices\":[1,2,9,18,25,41,45,58,64,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":191,\"vertices\":[3,6,11,16,30,32,35,53,66,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":192,\"vertices\":[10,14,15,18,25,32,40,45,50,64,77,88,89,91]},{\"tag\":\"block\",\"leaf\":193,\"vertices\":[2,7,8,13,31,41,45,50,56,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":194,\"vertices\":[10,15,16,19,30,32,40,50,53,64,77,79,89,91]},{\"tag\":\"block\",\"leaf\":195,\"vertices\":[10,14,15,18,30,32,40,50,53,64,77,83,89,91]},{\"tag\":\"block\",\"leaf\":196,\"vertices\":[4,10,11,15,25,32,40,50,62,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":197,\"vertices\":[2,7,8,13,31,41,44,50,53,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":198,\"vertices\":[3,10,11,16,25,32,39,50,62,77,82,88,89,91]},{\"tag\":\"block\",\"leaf\":199,\"vertices\":[1,2,7,18,30,41,50,53,64,77,82,83,89,91]},{\"tag\":\"block\",\"leaf\":200,\"vertices\":[2,3,10,18,25,32,45,50,64,77,82,88,89,91]},{\"tag\":\"block\",\"leaf\":201,\"vertices\":[2,3,10,18,30,32,50,53,64,77,82,83,89,91]},{\"tag\":\"block\",\"leaf\":202,\"vertices\":[1,2,7,18,25,41,45,50,64,77,82,88,89,91]},{\"tag\":\"block\",\"leaf\":203,\"vertices\":[3,10,11,16,30,32,35,50,53,77,82,89,90,91]},{\"tag\":\"block\",\"leaf\":204,\"vertices\":[10,13,15,18,27,32,40,44,57,65,81,85,87,88]},{\"tag\":\"block\",\"leaf\":205,\"vertices\":[10,13,15,18,30,32,40,57,65,69,73,81,85,87]},{\"tag\":\"block\",\"leaf\":206,\"vertices\":[2,7,13,17,31,41,44,57,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":207,\"vertices\":[0,2,10,18,32,38,44,57,65,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":208,\"vertices\":[2,7,11,13,31,41,45,57,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":209,\"vertices\":[2,7,11,16,29,30,41,57,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":210,\"vertices\":[10,15,17,18,30,32,40,57,65,69,77,81,85,87]},{\"tag\":\"block\",\"leaf\":211,\"vertices\":[10,15,16,17,30,32,40,57,65,69,77,79,85,87]},{\"tag\":\"block\",\"leaf\":212,\"vertices\":[10,13,15,18,27,32,40,44,57,65,81,84,86,88]},{\"tag\":\"block\",\"leaf\":213,\"vertices\":[10,13,15,18,30,32,40,57,65,69,73,81,84,86]},{\"tag\":\"block\",\"leaf\":214,\"vertices\":[2,7,13,17,31,41,44,57,65,76,82,84,86,90]},{\"tag\":\"block\",\"leaf\":215,\"vertices\":[0,2,10,18,32,38,44,57,65,77,81,84,86,88]},{\"tag\":\"block\",\"leaf\":216,\"vertices\":[2,7,11,13,31,41,45,57,65,73,82,84,86,90]},{\"tag\":\"block\",\"leaf\":217,\"vertices\":[2,7,11,16,29,30,41,57,65,73,82,84,86,90]},{\"tag\":\"block\",\"leaf\":218,\"vertices\":[10,15,17,18,30,32,40,57,65,69,77,81,84,86]},{\"tag\":\"block\",\"leaf\":219,\"vertices\":[10,15,16,17,30,32,40,57,65,69,77,79,84,86]},{\"tag\":\"block\",\"leaf\":220,\"vertices\":[10,17,18,19,27,32,40,44,57,65,71,81,89,91]},{\"tag\":\"block\",\"leaf\":221,\"vertices\":[10,12,17,18,30,32,40,57,65,69,71,81,89,91]},{\"tag\":\"block\",\"leaf\":222,\"vertices\":[3,13,17,18,31,39,52,57,65,69,76,82,89,91]},{\"tag\":\"block\",\"leaf\":223,\"vertices\":[10,15,17,18,30,32,40,57,65,69,77,81,89,91]},{\"tag\":\"block\",\"leaf\":224,\"vertices\":[11,15,18,19,29,30,40,52,57,65,73,81,89,91]},{\"tag\":\"block\",\"leaf\":225,\"vertices\":[10,11,18,19,30,32,40,57,65,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":226,\"vertices\":[3,13,16,18,31,39,52,57,65,69,73,82,89,91]},{\"tag\":\"block\",\"leaf\":227,\"vertices\":[10,15,16,17,30,32,40,57,65,69,77,79,89,91]},{\"tag\":\"block\",\"leaf\":228,\"vertices\":[4,13,15,18,31,40,52,57,65,69,73,81,89,91]},{\"tag\":\"block\",\"leaf\":229,\"vertices\":[3,13,15,17,31,39,52,57,65,69,76,79,89,91]},{\"tag\":\"block\",\"leaf\":230,\"vertices\":[10,13,15,18,30,32,40,57,65,69,73,81,89,91]},{\"tag\":\"block\",\"leaf\":231,\"vertices\":[10,14,16,18,30,32,40,57,65,69,71,73,89,91]},{\"tag\":\"block\",\"leaf\":232,\"vertices\":[10,12,16,17,30,32,40,57,65,69,71,79,89,91]},{\"tag\":\"block\",\"leaf\":233,\"vertices\":[2,3,10,18,30,32,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":234,\"vertices\":[2,4,7,18,31,41,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":235,\"vertices\":[1,2,7,18,30,41,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":236,\"vertices\":[2,4,7,17,31,41,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":237,\"vertices\":[4,7,10,18,31,40,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":238,\"vertices\":[3,7,10,17,31,39,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":239,\"vertices\":[4,10,11,18,27,32,40,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":240,\"vertices\":[10,14,16,17,27,32,40,44,57,65,71,89,90,91]},{\"tag\":\"block\",\"leaf\":241,\"vertices\":[10,14,16,18,27,32,40,44,57,65,71,88,89,91]},{\"tag\":\"block\",\"leaf\":242,\"vertices\":[0,2,3,17,29,44,52,57,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":243,\"vertices\":[0,2,10,18,32,38,44,57,65,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":244,\"vertices\":[2,12,13,18,31,38,44,52,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":245,\"vertices\":[2,3,10,18,27,32,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":246,\"vertices\":[2,7,12,18,31,41,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":247,\"vertices\":[1,2,7,18,27,41,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":248,\"vertices\":[2,7,13,17,31,41,44,57,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":249,\"vertices\":[10,13,15,18,27,32,40,44,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":250,\"vertices\":[2,3,13,17,31,44,52,57,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":251,\"vertices\":[2,13,14,17,31,38,44,52,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":252,\"vertices\":[3,13,15,17,31,37,44,52,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":253,\"vertices\":[13,14,15,17,31,40,44,52,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":254,\"vertices\":[2,7,14,17,31,41,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":255,\"vertices\":[7,10,14,17,31,40,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":256,\"vertices\":[3,7,10,17,31,37,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":257,\"vertices\":[4,10,11,16,27,32,40,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":258,\"vertices\":[2,3,11,16,29,30,52,57,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":259,\"vertices\":[2,7,11,16,29,30,41,57,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":260,\"vertices\":[11,14,15,16,29,30,40,52,57,65,73,89,90,91]},{\"tag\":\"block\",\"leaf\":261,\"vertices\":[3,10,11,16,27,32,39,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":262,\"vertices\":[10,11,14,16,30,32,40,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":263,\"vertices\":[3,10,11,16,30,32,37,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":264,\"vertices\":[2,3,11,13,31,45,52,57,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":265,\"vertices\":[2,7,11,13,31,41,45,57,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":266,\"vertices\":[11,13,14,15,31,40,45,52,57,65,73,89,90,91]},{\"tag\":\"block\",\"leaf\":267,\"vertices\":[2,7,11,14,31,41,45,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":268,\"vertices\":[2,7,11,12,31,41,45,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":269,\"vertices\":[7,10,11,14,31,40,45,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":270,\"vertices\":[10,13,14,15,31,40,45,56,58,65,73,85,87,90]},{\"tag\":\"block\",\"leaf\":271,\"vertices\":[10,13,14,15,31,40,44,53,58,65,76,85,87,90]},{\"tag\":\"block\",\"leaf\":272,\"vertices\":[2,3,10,13,31,45,56,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":273,\"vertices\":[2,3,10,13,31,44,53,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":274,\"vertices\":[4,13,15,16,31,37,41,56,58,65,73,85,87,90]},{\"tag\":\"block\",\"leaf\":275,\"vertices\":[2,13,14,15,31,41,45,56,58,65,73,85,87,90]},{\"tag\":\"block\",\"leaf\":276,\"vertices\":[8,13,15,18,27,32,40,44,57,66,81,85,87,88]},{\"tag\":\"block\",\"leaf\":277,\"vertices\":[2,13,14,15,31,41,44,53,58,65,76,85,87,90]},{\"tag\":\"block\",\"leaf\":278,\"vertices\":[11,13,15,19,31,39,41,53,58,65,76,79,85,87]},{\"tag\":\"block\",\"leaf\":279,\"vertices\":[8,13,15,18,30,32,40,57,66,69,73,81,85,87]},{\"tag\":\"block\",\"leaf\":280,\"vertices\":[2,13,18,19,31,41,45,56,58,65,73,82,85,87]},{\"tag\":\"block\",\"leaf\":281,\"vertices\":[2,13,18,19,31,41,44,53,58,65,76,82,85,87]},{\"tag\":\"block\",\"leaf\":282,\"vertices\":[1,2,11,18,25,41,45,58,65,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":283,\"vertices\":[1,2,11,18,30,41,53,58,65,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":284,\"vertices\":[2,5,13,17,31,41,44,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":285,\"vertices\":[0,2,8,18,32,38,44,57,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":286,\"vertices\":[1,2,11,17,25,41,45,58,65,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":287,\"vertices\":[2,4,11,17,25,29,41,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":288,\"vertices\":[2,12,13,17,31,41,45,56,58,65,82,85,87,90]},{\"tag\":\"block\",\"leaf\":289,\"vertices\":[0,2,3,18,32,45,57,64,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":290,\"vertices\":[1,2,11,16,30,41,53,58,65,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":291,\"vertices\":[2,4,11,13,31,41,53,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":292,\"vertices\":[2,12,13,16,31,41,44,53,58,65,82,85,87,90]},{\"tag\":\"block\",\"leaf\":293,\"vertices\":[0,2,3,16,32,44,57,62,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":294,\"vertices\":[0,2,3,15,32,44,57,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":295,\"vertices\":[2,5,11,13,31,41,45,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":296,\"vertices\":[2,5,11,16,29,30,41,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":297,\"vertices\":[2,4,13,16,31,41,56,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":298,\"vertices\":[0,2,3,15,32,45,57,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":299,\"vertices\":[0,2,4,16,32,38,57,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":300,\"vertices\":[3,11,16,17,30,32,35,57,66,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":301,\"vertices\":[11,17,18,19,30,32,35,38,57,66,77,81,85,87]},{\"tag\":\"block\",\"leaf\":302,\"vertices\":[11,14,16,17,30,32,35,38,57,66,77,85,87,90]},{\"tag\":\"block\",\"leaf\":303,\"vertices\":[11,15,17,19,30,32,40,57,62,66,77,81,85,87]},{\"tag\":\"block\",\"leaf\":304,\"vertices\":[11,14,15,17,30,32,40,57,62,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":305,\"vertices\":[2,3,11,17,30,32,57,62,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":306,\"vertices\":[2,3,17,18,30,32,57,64,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":307,\"vertices\":[2,14,17,18,30,32,38,57,64,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":308,\"vertices\":[3,15,17,18,30,32,37,57,64,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":309,\"vertices\":[14,15,17,18,30,32,40,57,64,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":310,\"vertices\":[15,16,17,19,30,32,40,57,64,66,77,79,85,87]},{\"tag\":\"block\",\"leaf\":311,\"vertices\":[2,16,17,19,30,32,38,57,64,66,77,79,85,87]},{\"tag\":\"block\",\"leaf\":312,\"vertices\":[8,15,17,18,30,32,40,57,66,69,77,81,85,87]},{\"tag\":\"block\",\"leaf\":313,\"vertices\":[8,15,16,17,30,32,40,57,66,69,77,79,85,87]},{\"tag\":\"block\",\"leaf\":314,\"vertices\":[3,16,17,18,30,32,35,57,66,69,77,82,85,87]},{\"tag\":\"block\",\"leaf\":315,\"vertices\":[3,15,17,18,30,32,35,57,66,69,77,81,85,87]},{\"tag\":\"edge\",\"edge\":8,\"owners\":[6,7,9,10,23,32,41,50,52,57,58,65,66]},{\"tag\":\"edge\",\"edge\":23,\"owners\":[6,7,23,32,50,52,57,58,72,85,86,87,89]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[6,9,50,57,58,65,66,85,86,89,91]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[7,10,32,41,52,58,66,72,86,87,89,91]}]}"
  "p cnf 221 1198\n-23 -2 0\n-26 -1 0\n-28 -1 0\n-28 -26 0\n-30 -2 0\n-30 -23 0\n-30 -28 0\n-31 -1 0\n-31 -26 0\n-31 -28 0\n-32 -2 0\n-32 -21 0\n-32 -22 0\n-32 -23 0\n-32 -24 0\n-32 -26 0\n-32 -28 0\n-32 -30 0\n-32 -31 0\n-33 -2 0\n-33 -24 0\n-33 -30 0\n-33 -32 0\n-36 -21 0\n-36 -26 0\n-38 -3 0\n-38 -15 0\n-38 -22 0\n-38 -28 0\n-38 -30 0\n-38 -36 0\n-39 -23 0\n-39 -28 0\n-39 -30 0\n-39 -38 0\n-40 -3 0\n-40 -5 0\n-40 -31 0\n-40 -36 0\n-40 -38 0\n-41 -3 0\n-41 -21 0\n-41 -22 0\n-41 -23 0\n-41 -24 0\n-41 -36 0\n-41 -38 0\n-41 -39 0\n-41 -40 0\n-42 -4 0\n-42 -23 0\n-42 -24 0\n-42 -33 0\n-42 -39 0\n-42 -41 0\n-45 -21 0\n-45 -26 0\n-45 -31 0\n-45 -36 0\n-45 -40 0\n-46 -22 0\n-46 -28 0\n-46 -30 0\n-46 -31 0\n-46 -38 0\n-46 -39 0\n-46 -40 0\n-46 -45 0\n-49 -30 0\n-50 -42 0\n-51 -21 0\n-51 -22 0\n-51 -23 0\n-51 -24 0\n-51 -49 0\n-51 -50 0\n-53 -21 0\n-53 -22 0\n-53 -23 0\n-53 -24 0\n-53 -33 0\n-53 -42 0\n-53 -51 0\n-54 -18 0\n-54 -22 0\n-54 -26 0\n-54 -28 0\n-54 -30 0\n-54 -38 0\n-54 -39 0\n-54 -46 0\n-57 -6 0\n-57 -26 0\n-57 -31 0\n-57 -45 0\n-57 -54 0\n-58 -21 0\n-58 -26 0\n-58 -49 0\n-58 -50 0\n-58 -51 0\n-58 -54 0\n-58 -57 0\n-59 -7 0\n-59 -8 0\n-59 -24 0\n-59 -33 0\n-59 -50 0\n-59 -53 0\n-59 -58 0\n-63 -9 0\n-63 -22 0\n-63 -28 0\n-63 -30 0\n-63 -36 0\n-63 -38 0\n-63 -39 0\n-63 -46 0\n-63 -49 0\n-63 -54 0\n-65 -12 0\n-65 -36 0\n-65 -40 0\n-65 -45 0\n-65 -57 0\n-65 -63 0\n-66 -21 0\n-66 -36 0\n-66 -49 0\n-66 -50 0\n-66 -51 0\n-66 -63 0\n-66 -65 0\n-67 -24 0\n-67 -42 0\n-67 -51 0\n-67 -53 0\n-67 -59 0\n-67 -66 0\n-70 -28 0\n-70 -30 0\n-70 -38 0\n-70 -39 0\n-70 -45 0\n-70 -46 0\n-70 -54 0\n-70 -57 0\n-70 -63 0\n-70 -65 0\n-71 -45 0\n-71 -51 0\n-71 -53 0\n-72 -14 0\n-72 -16 0\n-72 -21 0\n-72 -23 0\n-72 -30 0\n-72 -39 0\n-72 -50 0\n-72 -51 0\n-72 -53 0\n-73 -30 0\n-73 -33 0\n-73 -39 0\n-73 -42 0\n-73 -51 0\n-73 -53 0\n-73 -72 0\n-74 -26 0\n-74 -28 0\n-74 -36 0\n-74 -45 0\n-74 -54 0\n-77 -13 0\n-77 -28 0\n-77 -31 0\n-77 -46 0\n-77 -57 0\n-77 -74 0\n-78 -22 0\n-78 -28 0\n-78 -30 0\n-78 -32 0\n-78 -71 0\n-78 -72 0\n-78 -74 0\n-78 -77 0\n-80 -15 0\n-80 -19 0\n-80 -26 0\n-80 -36 0\n-80 -38 0\n-80 -45 0\n-80 -63 0\n-80 -74 0\n-82 -38 0\n-82 -40 0\n-82 -46 0\n-82 -65 0\n-82 -77 0\n-82 -80 0\n-83 -22 0\n-83 -38 0\n-83 -39 0\n-83 -41 0\n-83 -71 0\n-83 -72 0\n-83 -80 0\n-83 -82 0\n-84 -17 0\n-84 -26 0\n-84 -36 0\n-84 -45 0\n-84 -46 0\n-84 -70 0\n-84 -74 0\n-84 -77 0\n-84 -80 0\n-84 -82 0\n-85 -59 0\n-85 -67 0\n-86 -22 0\n-86 -23 0\n-86 -24 0\n-86 -50 0\n-86 -51 0\n-86 -71 0\n-86 -72 0\n-87 -51 0\n-87 -59 0\n-87 -72 0\n-89 -18 0\n-89 -31 0\n-89 -54 0\n-89 -57 0\n-89 -70 0\n-89 -74 0\n-89 -77 0\n-89 -84 0\n-90 -59 0\n-90 -67 0\n-91 -40 0\n-91 -63 0\n-91 -65 0\n-91 -70 0\n-91 -80 0\n-91 -82 0\n-91 -84 0\n-91 -89 0\n-92 -67 0\n-1 2 21 22 23 24 25 27 29 30 33 0\n-2 1 21 22 24 25 26 27 28 29 31 0\n-26 2 22 23 24 29 30 33 0\n-28 2 21 23 24 27 33 0\n-30 1 21 24 26 27 31 0\n-31 2 21 22 23 24 25 30 33 0\n-33 1 21 22 25 26 27 28 29 31 0\n-1 -2 -24 0\n-2 -24 -26 0\n-2 -24 -31 0\n-26 5 37 40 46 47 0\n-28 5 35 40 45 0\n-32 5 35 37 40 43 45 46 0\n-40 1 26 28 32 43 47 0\n-45 1 28 32 37 47 0\n-46 1 26 32 35 0\n-28 6 57 58 0\n-31 6 54 58 61 0\n-32 6 54 57 58 60 0\n-54 1 31 32 0\n-57 1 28 32 61 0\n-58 1 28 31 32 60 61 0\n-1 13 74 76 77 78 0\n-31 13 74 78 0\n-32 13 74 76 77 0\n-74 1 31 32 0\n-77 1 26 32 0\n-78 1 26 31 76 0\n-2 4 39 41 42 47 48 0\n-32 4 39 41 42 48 0\n-33 4 39 41 47 48 0\n-39 2 32 33 0\n-41 2 30 32 33 47 0\n-42 2 30 32 47 48 0\n-2 8 50 52 53 56 59 61 0\n-8 2 23 30 32 50 52 56 61 0\n-23 8 56 59 61 0\n-32 8 50 52 53 56 59 0\n-53 2 30 32 56 61 0\n-59 2 23 30 32 52 61 0\n-2 14 72 73 78 0\n-32 14 72 73 0\n-33 14 72 78 0\n-72 2 32 33 0\n-78 2 23 33 73 0\n-2 -73 -78 0\n-4 3 21 22 24 34 35 36 37 38 40 0\n-23 3 34 35 36 37 38 40 0\n-36 4 22 23 24 37 39 42 0\n-38 4 21 23 24 35 42 0\n-39 3 21 24 35 36 40 0\n-40 4 21 22 23 24 34 39 42 0\n-42 3 21 22 34 35 36 37 38 40 0\n-3 -4 -24 0\n-21 -40 -42 0\n-22 -36 -42 0\n-22 -40 -42 0\n-3 5 27 29 31 44 45 46 48 0\n-5 3 27 29 36 38 41 44 48 0\n-31 3 36 38 41 44 48 0\n-36 5 29 31 46 48 0\n-41 5 27 29 31 44 45 46 0\n-45 3 29 38 41 48 0\n-46 3 27 36 41 0\n-40 9 63 66 69 0\n-41 9 63 65 66 68 0\n-65 3 38 41 69 0\n-66 3 38 40 41 68 69 0\n-36 15 82 83 0\n-40 15 80 83 0\n-41 15 80 81 82 0\n-80 3 40 41 0\n-82 3 36 41 0\n-83 3 36 40 81 0\n-11 4 23 39 41 50 52 64 69 0\n-41 11 50 52 53 64 67 0\n-53 4 39 41 64 69 0\n-67 4 23 39 41 52 69 0\n-41 16 72 73 0\n-42 16 72 83 0\n-72 4 41 42 0\n-83 4 23 42 73 0\n-16 -41 -73 0\n-12 5 31 40 46 60 68 0\n-31 12 65 68 70 0\n-40 12 57 60 70 0\n-46 12 57 65 0\n-57 5 40 46 68 0\n-65 5 31 46 60 0\n-70 5 31 40 0\n-31 17 81 82 84 0\n-40 17 76 77 84 0\n-45 17 77 82 0\n-77 5 40 45 81 0\n-82 5 31 45 76 0\n-6 7 21 25 27 49 50 51 55 56 59 0\n-51 6 25 26 27 54 55 56 57 0\n-54 7 21 27 50 51 59 0\n-57 7 21 25 49 50 51 56 59 0\n-59 6 21 25 26 27 49 54 55 57 0\n-12 6 26 35 43 54 58 62 0\n-26 12 62 65 70 0\n-45 6 54 58 62 0\n-54 12 35 45 65 0\n-58 12 35 43 45 62 65 70 0\n-65 6 26 43 54 58 0\n-6 18 74 76 89 0\n-26 18 89 0\n-57 18 74 0\n-58 18 74 76 89 0\n-74 6 57 58 0\n-89 6 26 58 0\n-7 8 24 33 53 0\n-8 7 24 51 58 0\n-33 7 51 58 0\n-51 8 33 0\n-53 7 58 0\n-58 8 24 33 53 0\n-58 10 66 67 0\n-59 10 66 0\n-66 7 58 59 0\n-67 7 58 0\n-7 86 87 90 0\n-51 90 0\n-58 86 87 90 0\n-59 86 0\n-86 7 58 59 0\n-90 7 51 58 0\n-8 11 42 67 0\n-33 11 67 0\n-42 8 59 0\n-59 11 42 0\n-67 8 33 0\n-8 73 87 88 90 0\n-33 87 88 90 0\n-53 90 0\n-59 73 88 0\n-88 8 33 59 0\n-90 8 33 53 73 0\n-9 10 21 34 35 49 50 51 62 64 67 0\n-51 9 34 35 36 62 63 64 65 0\n-63 10 21 35 50 51 67 0\n-65 10 21 34 49 50 51 64 67 0\n-67 9 21 34 35 36 49 62 63 65 0\n-9 12 27 44 45 55 57 70 0\n-36 12 55 57 70 0\n-63 12 27 45 57 0\n-66 12 27 44 45 55 57 70 0\n-70 9 27 36 66 0\n-36 19 91 0\n-65 19 80 0\n-66 19 80 81 91 0\n-80 9 65 66 0\n-91 9 36 66 0\n-42 10 51 66 0\n-51 11 42 0\n-53 10 66 0\n-66 11 24 42 53 0\n-10 86 87 92 0\n-51 92 0\n-66 86 87 92 0\n-67 86 0\n-92 10 51 66 0\n-11 73 87 88 92 0\n-42 87 88 92 0\n-53 92 0\n-67 73 88 0\n-87 11 42 0\n-92 11 42 53 73 0\n-57 20 81 84 91 0\n-65 20 76 84 89 0\n-84 12 57 65 0\n-89 12 45 65 81 0\n-91 12 45 57 76 0\n-13 14 22 25 29 30 71 72 75 0\n-14 13 22 25 28 29 71 74 75 77 0\n-28 14 71 72 75 0\n-30 13 71 74 75 77 0\n-72 13 25 28 29 74 75 77 0\n-74 14 22 29 30 72 0\n-77 14 22 25 30 71 72 0\n-28 17 79 82 84 0\n-46 13 74 78 79 0\n-74 17 37 46 47 82 0\n-78 17 37 43 46 79 82 84 0\n-82 13 28 43 47 74 78 0\n-84 13 28 37 47 78 0\n-18 13 28 60 61 77 78 0\n-28 18 89 0\n-54 13 77 78 0\n-77 18 54 61 0\n-78 18 54 60 89 0\n-89 13 28 61 78 0\n-14 16 39 47 48 83 0\n-16 14 30 47 48 78 0\n-30 16 83 0\n-39 14 78 0\n-78 16 39 48 83 0\n-83 14 30 47 78 0\n-30 85 88 90 0\n-72 56 61 90 0\n-78 52 56 85 88 90 0\n-88 14 30 56 61 78 0\n-15 16 22 34 37 39 71 72 79 0\n-16 15 22 34 37 38 71 79 80 82 0\n-38 16 71 72 79 0\n-39 15 71 79 80 82 0\n-72 15 34 37 38 79 80 82 0\n-80 16 22 37 39 72 0\n-82 16 22 34 39 71 72 0\n-38 17 75 77 84 0\n-46 15 75 80 83 0\n-80 17 29 46 48 77 0\n-83 17 29 44 46 75 77 84 0\n-84 15 29 38 48 83 0\n-19 15 38 68 69 82 83 0\n-38 19 91 0\n-63 15 82 83 0\n-82 19 63 69 0\n-83 19 63 68 91 0\n-91 15 38 69 83 0\n-16 52 64 69 85 88 92 0\n-72 64 69 92 0\n-83 52 64 85 88 92 0\n-88 16 39 64 69 83 0\n-17 20 60 68 70 89 91 0\n-46 20 89 91 0\n-70 17 77 82 0\n-77 20 68 70 91 0\n-82 20 60 70 89 0\n-89 17 46 68 82 0\n-91 17 46 60 77 0\n-18 25 49 55 56 71 75 85 86 90 0\n-54 71 75 85 86 90 0\n-74 49 55 56 85 86 90 0\n-86 18 25 54 55 56 74 75 89 0\n-89 25 49 56 71 85 86 90 0\n-90 18 25 49 54 55 71 74 75 89 0\n-49 -89 -90 0\n-71 -89 -90 0\n-54 20 79 84 91 0\n-70 18 74 79 0\n-74 20 62 70 91 0\n-84 18 54 62 0\n-91 18 43 54 74 0\n-80 49 62 64 85 86 92 0\n-86 19 34 62 63 64 79 80 91 0\n-92 19 34 49 62 63 71 79 80 91 0\n-63 20 75 84 89 0\n-70 19 75 80 0\n-80 20 55 70 89 0\n-84 19 55 63 0\n-89 19 44 63 80 0\n-21 71 0\n-71 21 0\n-22 49 52 0\n-49 22 52 0\n-52 22 49 0\n-24 73 0\n-73 24 0\n-25 34 43 44 0\n-34 25 43 44 0\n-43 25 34 44 0\n-44 25 34 43 0\n-27 75 76 0\n-75 27 76 0\n-76 27 75 0\n-29 55 60 0\n-55 29 60 0\n-60 29 55 0\n-35 79 81 0\n-79 35 81 0\n-81 35 79 0\n-37 62 68 0\n-62 37 68 0\n-68 37 62 0\n-47 61 0\n-61 47 0\n-48 69 0\n-69 48 0\n-87 50 85 0\n-56 64 0\n-64 56 0\n-86 88 0\n-88 86 0\n-90 92 0\n-92 90 0\n-93 1 0\n-1 93 0\n-94 2 0\n-2 94 0\n-95 3 0\n-3 95 0\n-96 4 0\n-4 96 0\n-97 5 0\n-5 97 0\n-98 6 0\n-6 98 0\n-99 7 0\n-7 99 0\n-100 8 0\n-8 100 0\n-101 9 0\n-9 101 0\n-10 102 0\n-103 11 0\n-11 103 0\n-104 12 0\n-12 104 0\n-13 105 0\n-106 14 0\n-14 106 0\n-107 15 0\n-15 107 0\n-16 108 0\n-17 109 0\n-18 110 0\n-19 111 0\n-20 112 0\n-113 93 94 0\n-94 113 0\n-93 113 0\n-93 -94 114 0\n-115 96 97 0\n-97 115 0\n-96 115 0\n-96 -97 116 0\n-117 95 115 0\n-115 117 0\n-95 117 0\n-95 -115 118 0\n-95 -116 119 0\n-120 113 117 0\n-117 120 0\n-118 121 0\n-119 122 0\n-113 120 0\n-113 -117 121 0\n-113 -118 122 0\n-113 -119 123 0\n-114 121 0\n-114 -117 122 0\n-114 -118 123 0\n-124 98 99 0\n-99 124 0\n-98 124 0\n-98 -99 125 0\n-102 126 0\n-127 101 0\n-101 126 0\n-101 -102 127 0\n-126 128 0\n-129 100 127 0\n-127 129 0\n-100 128 0\n-100 -126 129 0\n-100 -127 130 0\n-128 131 0\n-132 124 129 0\n-129 132 0\n-130 133 0\n-124 131 0\n-124 -128 132 0\n-125 132 0\n-125 -128 133 0\n-131 134 0\n-135 120 132 0\n-132 135 0\n-120 134 0\n-120 -131 135 0\n-120 -132 136 0\n-120 -133 137 0\n-121 135 0\n-121 -131 136 0\n-121 -132 137 0\n-122 136 0\n-122 -131 137 0\n-122 -132 138 0\n-123 137 0\n-123 -131 138 0\n-139 103 104 0\n-104 139 0\n-103 139 0\n-103 -104 140 0\n-141 106 107 0\n-107 141 0\n-106 141 0\n-106 -107 142 0\n-141 143 0\n-142 144 0\n-105 143 0\n-144 141 0\n-105 -141 144 0\n-143 145 0\n-146 139 144 0\n-144 146 0\n-139 145 0\n-139 -143 146 0\n-139 -144 147 0\n-140 146 0\n-140 -143 147 0\n-109 148 0\n-108 148 0\n-108 -109 149 0\n-112 150 0\n-111 150 0\n-111 -112 151 0\n-150 152 0\n-151 153 0\n-110 152 0\n-110 -150 153 0\n-110 -151 154 0\n-152 155 0\n-153 156 0\n-154 157 0\n-148 155 0\n-148 -152 156 0\n-148 -153 157 0\n-149 156 0\n-149 -152 157 0\n-155 158 0\n-156 159 0\n-157 160 0\n-145 158 0\n-145 -155 159 0\n-145 -156 160 0\n-145 -157 161 0\n-146 159 0\n-146 -155 160 0\n-146 -156 161 0\n-146 -157 162 0\n-147 -155 161 0\n-147 -156 162 0\n-162 163 0\n-134 -161 163 0\n-135 -160 163 0\n-136 -159 163 0\n-137 -158 163 0\n-138 163 0\n-163 0\n-164 51 58 59 0\n-51 164 0\n-58 164 0\n-59 164 0\n-165 66 67 0\n-66 165 0\n-67 165 0\n-166 23 33 42 53 0\n-33 166 0\n-42 166 0\n-53 166 0\n-167 28 30 32 78 0\n-28 167 0\n-30 167 0\n-32 167 0\n-78 167 0\n-168 39 72 83 0\n-39 168 0\n-72 168 0\n-83 168 0\n-169 31 57 77 89 0\n-31 169 0\n-57 169 0\n-77 169 0\n-89 169 0\n-170 36 38 40 41 0\n-36 170 0\n-38 170 0\n-40 170 0\n-41 170 0\n-171 46 54 63 70 0\n-46 171 0\n-54 171 0\n-63 171 0\n-70 171 0\n-172 26 45 74 80 84 0\n-45 172 0\n-74 172 0\n-80 172 0\n-173 65 82 91 0\n-65 173 0\n-82 173 0\n-91 173 0\n-174 164 165 0\n-175 164 0\n-175 165 0\n-164 -165 175 0\n-176 167 168 0\n-168 176 0\n-177 167 0\n-167 176 0\n-177 168 0\n-167 -168 177 0\n-178 166 176 0\n-179 166 177 0\n-180 166 0\n-179 176 0\n-166 -176 179 0\n-180 177 0\n-166 -177 180 0\n-181 174 180 0\n-182 174 0\n-181 175 179 0\n-182 175 180 0\n-183 175 0\n-181 178 0\n-182 179 0\n-175 -179 182 0\n-183 180 0\n-175 -180 183 0\n-184 169 170 0\n-185 169 0\n-169 184 0\n-185 170 0\n-169 -170 185 0\n-186 172 173 0\n-173 186 0\n-187 172 0\n-172 186 0\n-187 173 0\n-172 -173 187 0\n-188 171 186 0\n-189 171 187 0\n-187 189 0\n-190 171 0\n-189 186 0\n-171 -186 189 0\n-190 187 0\n-171 -187 190 0\n-191 184 190 0\n-192 184 0\n-191 185 189 0\n-192 185 190 0\n-184 -190 192 0\n-193 185 0\n-191 188 0\n-192 189 0\n-185 -189 192 0\n-193 190 0\n-185 -190 193 0\n-194 181 0\n-194 182 193 0\n-194 183 192 0\n-182 -193 195 0\n-194 191 0\n-183 -192 195 0\n194 0\n-195 0\n-50 196 0\n-86 196 0\n-90 196 0\n-85 197 0\n-88 197 0\n-92 197 0\n-198 21 22 24 87 0\n-21 198 0\n-22 198 0\n-24 198 0\n-87 198 0\n-199 49 71 73 0\n-49 199 0\n-71 199 0\n-73 199 0\n-200 25 27 35 0\n-25 200 0\n-27 200 0\n-35 200 0\n-201 34 75 79 0\n-34 201 0\n-75 201 0\n-79 201 0\n-202 43 76 81 0\n-43 202 0\n-76 202 0\n-81 202 0\n-203 29 37 44 47 48 52 56 0\n-29 203 0\n-37 203 0\n-44 203 0\n-47 203 0\n-48 203 0\n-52 203 0\n-56 203 0\n-204 55 61 62 64 69 0\n-55 204 0\n-61 204 0\n-62 204 0\n-64 204 0\n-69 204 0\n-205 60 68 0\n-60 205 0\n-68 205 0\n-197 206 0\n-196 206 0\n-196 -197 207 0\n-208 199 200 0\n-200 208 0\n-199 208 0\n-209 198 208 0\n-208 209 0\n-198 209 0\n-209 210 0\n-206 210 0\n-206 -209 211 0\n-207 -209 212 0\n-213 201 202 0\n-202 213 0\n-201 213 0\n-201 -202 214 0\n-215 204 205 0\n-205 215 0\n-204 215 0\n-204 -205 216 0\n-217 203 215 0\n-216 218 0\n-203 217 0\n-203 -215 218 0\n-219 213 217 0\n-217 219 0\n-218 220 0\n-213 219 0\n-213 -217 220 0\n-214 220 0\n-210 -220 221 0\n-211 -219 221 0\n-212 221 0\n-221 0\n-1 -10 -11 -16 -33 -41 -46 -58 -65 -78 -80 -86 -88 -89 0\n-1 -10 -11 -16 -33 -41 -45 -58 -63 -78 -82 -86 -88 -89 0\n-1 -10 -11 -16 -33 -41 -46 -58 -65 -78 -80 -85 -87 -89 0\n-1 -10 -11 -16 -33 -41 -45 -58 -63 -78 -82 -85 -87 -89 0\n-6 -7 -11 -19 -28 -33 -41 -45 -66 -72 -82 -89 -90 -92 0\n-6 -7 -11 -19 -31 -33 -41 -66 -70 -72 -74 -82 -90 -92 0\n-6 -7 -8 -18 -32 -40 -42 -66 -70 -72 -77 -80 -90 -92 0\n-7 -8 -12 -20 -32 -40 -42 -54 -66 -72 -77 -80 -90 -92 0\n-6 -7 -8 -18 -32 -38 -42 -45 -66 -72 -77 -90 -91 -92 0\n-1 -7 -11 -15 -33 -41 -45 -54 -66 -72 -77 -90 -91 -92 0\n-1 -2 -10 -16 -41 -45 -53 -58 -63 -78 -82 -89 -90 -92 0\n-1 -10 -11 -16 -33 -41 -45 -58 -63 -78 -82 -89 -90 -92 0\n-7 -14 -15 -16 -32 -41 -45 -53 -54 -66 -77 -90 -91 -92 0\n-1 -10 -11 -13 -33 -41 -45 -58 -63 -72 -82 -89 -90 -92 0\n-7 -8 -11 -15 -32 -41 -45 -54 -66 -72 -77 -90 -91 -92 0\n-1 -7 -11 -15 -33 -41 -46 -57 -66 -72 -74 -90 -91 -92 0\n-1 -2 -10 -16 -41 -46 -53 -58 -65 -78 -80 -89 -90 -92 0\n-1 -10 -11 -16 -33 -41 -46 -58 -65 -78 -80 -89 -90 -92 0\n-7 -14 -15 -16 -32 -41 -46 -53 -57 -66 -74 -90 -91 -92 0\n-1 -10 -11 -13 -33 -41 -46 -58 -65 -72 -80 -89 -90 -92 0\n-7 -8 -11 -15 -32 -41 -46 -57 -66 -72 -74 -90 -91 -92 0\n-5 -7 -8 -17 -32 -38 -42 -57 -66 -72 -74 -90 -91 -92 0\n-7 -16 -17 -20 -31 -33 -41 -54 -65 -67 -78 -80 -86 -88 0\n-7 -15 -16 -19 -31 -33 -41 -54 -65 -67 -78 -84 -86 -88 0\n-7 -15 -16 -19 -26 -33 -41 -46 -65 -67 -78 -86 -88 -89 0\n-1 -6 -7 -16 -33 -41 -46 -65 -67 -78 -80 -86 -88 -89 0\n-5 -7 -12 -16 -26 -33 -41 -63 -67 -78 -82 -86 -88 -89 0\n-1 -6 -7 -16 -33 -41 -45 -63 -67 -78 -82 -86 -88 -89 0\n-2 -10 -12 -17 -31 -36 -42 -54 -59 -78 -83 -86 -88 -91 0\n-1 -4 -7 -18 -33 -40 -57 -63 -67 -78 -83 -84 -86 -88 0\n-1 -2 -10 -18 -36 -42 -46 -57 -59 -78 -83 -86 -88 -91 0\n-1 -2 -10 -18 -40 -42 -57 -59 -63 -78 -83 -84 -86 -88 0\n-1 -4 -7 -18 -33 -36 -46 -57 -67 -78 -83 -86 -88 -91 0\n-2 -10 -12 -17 -26 -40 -42 -59 -63 -78 -83 -86 -88 -89 0\n-8 -13 -14 -18 -32 -36 -42 -46 -51 -57 -83 -90 -91 -92 0\n-1 -6 -11 -16 -33 -41 -46 -51 -65 -78 -80 -89 -90 -92 0\n-8 -14 -17 -20 -32 -40 -42 -51 -57 -63 -74 -83 -90 -92 0\n-8 -13 -14 -18 -32 -40 -42 -51 -57 -63 -83 -84 -90 -92 0\n-5 -8 -12 -14 -32 -36 -42 -51 -54 -77 -83 -90 -91 -92 0\n-1 -6 -11 -16 -33 -41 -45 -51 -63 -78 -82 -89 -90 -92 0\n-2 -8 -12 -17 -31 -36 -42 -51 -54 -78 -83 -90 -91 -92 0\n-1 -4 -11 -18 -33 -40 -51 -57 -63 -78 -83 -84 -90 -92 0\n-1 -2 -8 -18 -36 -42 -46 -51 -57 -78 -83 -90 -91 -92 0\n-1 -2 -8 -18 -40 -42 -51 -57 -63 -78 -83 -84 -90 -92 0\n-1 -4 -11 -18 -33 -36 -46 -51 -57 -78 -83 -90 -91 -92 0\n-2 -8 -12 -17 -26 -40 -42 -51 -63 -78 -83 -89 -90 -92 0\n-8 -14 -16 -18 -32 -38 -42 -45 -58 -66 -77 -86 -88 -91 0\n-8 -14 -16 -18 -32 -40 -42 -58 -66 -70 -77 -80 -86 -88 0\n-1 -11 -16 -19 -33 -41 -45 -58 -66 -78 -82 -86 -88 -89 0\n-1 -3 -8 -18 -30 -42 -45 -58 -66 -77 -83 -86 -88 -91 0\n-1 -11 -12 -16 -33 -41 -46 -58 -66 -78 -80 -86 -88 -89 0\n-1 -11 -12 -17 -33 -39 -40 -58 -66 -78 -80 -86 -88 -89 0\n-8 -14 -18 -19 -32 -40 -42 -58 -66 -70 -77 -83 -86 -88 0\n-8 -14 -17 -19 -32 -40 -42 -58 -66 -70 -74 -83 -86 -88 0\n-8 -14 -16 -18 -32 -38 -42 -45 -58 -66 -77 -85 -87 -91 0\n-8 -14 -16 -18 -32 -40 -42 -58 -66 -70 -77 -80 -85 -87 0\n-1 -11 -16 -19 -33 -41 -45 -58 -66 -78 -82 -85 -87 -89 0\n-1 -3 -8 -18 -30 -42 -45 -58 -66 -77 -83 -85 -87 -91 0\n-1 -11 -12 -16 -33 -41 -46 -58 -66 -78 -80 -85 -87 -89 0\n-1 -11 -12 -17 -33 -39 -40 -58 -66 -78 -80 -85 -87 -89 0\n-8 -14 -18 -19 -32 -40 -42 -58 -66 -70 -77 -83 -85 -87 0\n-8 -14 -17 -19 -32 -40 -42 -58 -66 -70 -74 -83 -85 -87 0\n-8 -18 -19 -20 -32 -38 -42 -45 -58 -66 -72 -77 -90 -92 0\n-8 -15 -18 -19 -32 -40 -42 -58 -66 -70 -72 -77 -90 -92 0\n-2 -16 -18 -19 -31 -41 -53 -58 -66 -70 -78 -82 -90 -92 0\n-8 -14 -18 -19 -32 -40 -42 -58 -66 -70 -77 -83 -90 -92 0\n-12 -14 -18 -20 -32 -39 -40 -53 -58 -66 -77 -80 -90 -92 0\n-8 -12 -18 -20 -32 -40 -42 -58 -66 -72 -77 -80 -90 -92 0\n-2 -16 -17 -18 -31 -41 -53 -58 -66 -70 -78 -80 -90 -92 0\n-8 -14 -17 -19 -32 -40 -42 -58 -66 -70 -74 -83 -90 -92 0\n-5 -14 -16 -18 -32 -41 -53 -58 -66 -70 -77 -80 -90 -92 0\n-2 -14 -16 -19 -31 -41 -53 -58 -66 -70 -74 -82 -90 -92 0\n-8 -14 -16 -18 -32 -40 -42 -58 -66 -70 -77 -80 -90 -92 0\n-8 -13 -17 -18 -32 -40 -42 -58 -66 -70 -72 -80 -90 -92 0\n-8 -15 -17 -19 -32 -40 -42 -58 -66 -70 -72 -74 -90 -92 0\n-1 -2 -8 -18 -40 -42 -58 -66 -70 -72 -77 -80 -90 -92 0\n-1 -5 -11 -18 -33 -41 -58 -66 -70 -72 -77 -80 -90 -92 0\n-1 -4 -11 -18 -33 -40 -58 -66 -70 -72 -77 -80 -90 -92 0\n-1 -5 -11 -19 -33 -41 -58 -66 -70 -72 -74 -82 -90 -92 0\n-5 -8 -11 -18 -32 -41 -58 -66 -70 -72 -77 -80 -90 -92 0\n-2 -8 -11 -19 -31 -41 -58 -66 -70 -72 -74 -82 -90 -92 0\n-5 -8 -12 -18 -32 -38 -42 -58 -66 -72 -77 -90 -91 -92 0\n-8 -13 -17 -19 -32 -38 -42 -45 -58 -66 -72 -89 -90 -92 0\n-8 -13 -17 -18 -32 -38 -42 -45 -58 -66 -72 -90 -91 -92 0\n-1 -2 -3 -19 -39 -45 -53 -58 -66 -78 -82 -89 -90 -92 0\n-1 -3 -8 -18 -30 -42 -45 -58 -66 -77 -83 -90 -91 -92 0\n-1 -15 -16 -18 -30 -41 -45 -53 -58 -66 -77 -90 -91 -92 0\n-1 -2 -8 -18 -38 -42 -45 -58 -66 -72 -77 -90 -91 -92 0\n-1 -11 -15 -18 -33 -41 -45 -58 -66 -72 -77 -90 -91 -92 0\n-1 -4 -11 -18 -33 -38 -45 -58 -66 -72 -77 -90 -91 -92 0\n-1 -11 -16 -19 -33 -41 -45 -58 -66 -78 -82 -89 -90 -92 0\n-8 -14 -16 -18 -32 -38 -42 -45 -58 -66 -77 -90 -91 -92 0\n-1 -2 -16 -19 -41 -45 -53 -58 -66 -78 -82 -89 -90 -92 0\n-1 -13 -16 -19 -30 -41 -45 -53 -58 -66 -82 -89 -90 -92 0\n-2 -14 -16 -19 -28 -41 -45 -53 -58 -66 -82 -89 -90 -92 0\n-13 -14 -16 -19 -32 -41 -45 -53 -58 -66 -82 -89 -90 -92 0\n-1 -11 -13 -19 -33 -41 -45 -58 -66 -72 -82 -89 -90 -92 0\n-8 -11 -13 -19 -32 -41 -45 -58 -66 -72 -82 -89 -90 -92 0\n-2 -8 -11 -19 -28 -41 -45 -58 -66 -72 -82 -89 -90 -92 0\n-5 -8 -12 -17 -32 -38 -42 -58 -66 -72 -74 -90 -91 -92 0\n-1 -2 -12 -17 -39 -40 -53 -58 -66 -78 -80 -89 -90 -92 0\n-1 -11 -12 -17 -33 -39 -40 -58 -66 -78 -80 -89 -90 -92 0\n-12 -13 -14 -17 -32 -39 -40 -53 -58 -66 -80 -89 -90 -92 0\n-2 -8 -12 -17 -31 -38 -42 -58 -66 -72 -74 -90 -91 -92 0\n-8 -12 -13 -17 -32 -40 -42 -58 -66 -72 -80 -89 -90 -92 0\n-2 -8 -12 -17 -28 -40 -42 -58 -66 -72 -80 -89 -90 -92 0\n-1 -2 -12 -16 -41 -46 -53 -58 -66 -78 -80 -89 -90 -92 0\n-1 -11 -12 -16 -33 -41 -46 -58 -66 -78 -80 -89 -90 -92 0\n-12 -13 -14 -16 -32 -41 -46 -53 -58 -66 -80 -89 -90 -92 0\n-1 -11 -12 -13 -33 -41 -46 -58 -66 -72 -80 -89 -90 -92 0\n-1 -11 -12 -15 -33 -41 -46 -58 -66 -72 -74 -90 -91 -92 0\n-8 -11 -12 -13 -32 -41 -46 -58 -66 -72 -80 -89 -90 -92 0\n-8 -13 -14 -16 -32 -41 -46 -58 -65 -67 -80 -86 -88 -89 0\n-8 -13 -14 -16 -32 -41 -45 -58 -63 -67 -82 -86 -88 -89 0\n-1 -2 -8 -16 -41 -46 -58 -65 -67 -78 -80 -86 -88 -89 0\n-1 -2 -8 -16 -41 -45 -58 -63 -67 -78 -82 -86 -88 -89 0\n-5 -14 -16 -17 -28 -33 -41 -58 -65 -67 -80 -86 -88 -89 0\n-1 -13 -14 -16 -33 -41 -46 -58 -65 -67 -80 -86 -88 -89 0\n-6 -14 -16 -18 -32 -38 -42 -45 -59 -66 -77 -86 -88 -91 0\n-1 -13 -14 -16 -33 -41 -45 -58 -63 -67 -82 -86 -88 -89 0\n-12 -14 -16 -20 -31 -33 -41 -58 -63 -67 -74 -82 -86 -88 0\n-6 -14 -16 -18 -32 -40 -42 -59 -66 -70 -77 -80 -86 -88 0\n-1 -16 -18 -20 -33 -41 -46 -58 -65 -67 -78 -80 -86 -88 0\n-1 -16 -18 -20 -33 -41 -45 -58 -63 -67 -78 -82 -86 -88 0\n-1 -4 -12 -18 -33 -36 -46 -58 -67 -78 -83 -86 -88 -91 0\n-1 -4 -12 -18 -33 -40 -58 -63 -67 -78 -83 -84 -86 -88 0\n-1 -9 -16 -19 -33 -41 -45 -58 -67 -78 -82 -86 -88 -89 0\n-1 -3 -6 -18 -30 -42 -45 -59 -66 -77 -83 -86 -88 -91 0\n-1 -4 -12 -19 -33 -36 -46 -58 -67 -78 -83 -86 -88 -89 0\n-1 -5 -12 -19 -33 -36 -39 -58 -67 -78 -82 -86 -88 -89 0\n-1 -15 -16 -19 -33 -41 -46 -58 -65 -67 -78 -86 -88 -89 0\n-1 -2 -3 -18 -42 -46 -57 -59 -66 -78 -83 -86 -88 -91 0\n-1 -4 -12 -17 -33 -40 -58 -63 -67 -78 -83 -86 -88 -89 0\n-1 -5 -12 -16 -33 -41 -58 -63 -67 -78 -82 -86 -88 -89 0\n-1 -15 -16 -17 -33 -41 -45 -58 -63 -67 -78 -86 -88 -89 0\n-1 -2 -3 -17 -42 -45 -54 -59 -66 -78 -83 -86 -88 -91 0\n-1 -2 -3 -14 -42 -45 -54 -59 -66 -77 -83 -86 -88 -91 0\n-1 -9 -12 -16 -33 -41 -46 -58 -67 -78 -80 -86 -88 -89 0\n-1 -9 -12 -17 -33 -39 -40 -58 -67 -78 -80 -86 -88 -89 0\n-1 -5 -16 -17 -33 -41 -58 -65 -67 -78 -80 -86 -88 -89 0\n-1 -2 -3 -14 -42 -46 -57 -59 -66 -74 -83 -86 -88 -91 0\n-1 -3 -5 -17 -30 -42 -57 -59 -66 -74 -83 -86 -88 -91 0\n-2 -12 -17 -19 -26 -40 -42 -59 -66 -78 -83 -86 -88 -89 0\n-12 -18 -19 -20 -26 -30 -40 -42 -59 -66 -77 -83 -86 -88 0\n-12 -13 -17 -19 -26 -30 -40 -42 -59 -66 -83 -86 -88 -89 0\n-12 -14 -19 -20 -32 -40 -42 -54 -59 -66 -77 -83 -86 -88 0\n-12 -13 -14 -19 -32 -40 -42 -54 -59 -66 -83 -84 -86 -88 0\n-1 -2 -12 -19 -40 -42 -54 -59 -66 -78 -83 -84 -86 -88 0\n-1 -2 -18 -19 -40 -42 -57 -59 -66 -78 -83 -84 -86 -88 0\n-1 -13 -18 -19 -30 -40 -42 -57 -59 -66 -83 -84 -86 -88 0\n-2 -14 -18 -19 -28 -40 -42 -57 -59 -66 -83 -84 -86 -88 0\n-13 -14 -18 -19 -32 -40 -42 -57 -59 -66 -83 -84 -86 -88 0\n-14 -17 -19 -20 -32 -40 -42 -57 -59 -66 -74 -83 -86 -88 0\n-1 -17 -19 -20 -30 -40 -42 -57 -59 -66 -74 -83 -86 -88 0\n-6 -14 -18 -19 -32 -40 -42 -59 -66 -70 -77 -83 -86 -88 0\n-6 -14 -17 -19 -32 -40 -42 -59 -66 -70 -74 -83 -86 -88 0\n-2 -17 -18 -19 -26 -40 -42 -59 -66 -70 -78 -83 -86 -88 0\n-2 -14 -18 -19 -26 -40 -42 -59 -66 -70 -77 -83 -86 -88 0\n-3 -7 -8 -14 -32 -42 -46 -57 -66 -74 -83 -86 -88 -91 0\n-3 -7 -8 -14 -32 -42 -45 -54 -66 -77 -83 -86 -88 -91 0\n-3 -7 -8 -14 -32 -42 -46 -57 -66 -74 -83 -85 -87 -91 0\n-3 -7 -8 -14 -32 -42 -45 -54 -66 -77 -83 -85 -87 -91 0\n-8 -9 -10 -18 -32 -38 -42 -45 -58 -72 -77 -90 -91 -92 0\n-8 -9 -10 -18 -32 -40 -42 -58 -70 -72 -77 -80 -90 -92 0\n-9 -10 -11 -19 -31 -33 -41 -58 -70 -72 -74 -82 -90 -92 0\n-10 -11 -12 -20 -31 -33 -41 -58 -63 -72 -74 -82 -90 -92 0\n-9 -10 -11 -19 -28 -33 -41 -45 -58 -72 -82 -89 -90 -92 0\n-3 -8 -10 -13 -32 -42 -45 -58 -63 -72 -82 -89 -90 -92 0\n-3 -4 -7 -14 -32 -45 -53 -54 -66 -77 -83 -90 -91 -92 0\n-3 -7 -8 -14 -32 -42 -45 -54 -66 -77 -83 -90 -91 -92 0\n-10 -13 -14 -16 -32 -41 -45 -53 -58 -63 -82 -89 -90 -92 0\n-3 -7 -8 -15 -32 -42 -45 -54 -66 -72 -77 -90 -91 -92 0\n-8 -10 -11 -13 -32 -41 -45 -58 -63 -72 -82 -89 -90 -92 0\n-3 -8 -10 -13 -32 -42 -46 -58 -65 -72 -80 -89 -90 -92 0\n-3 -4 -7 -14 -32 -46 -53 -57 -66 -74 -83 -90 -91 -92 0\n-3 -7 -8 -14 -32 -42 -46 -57 -66 -74 -83 -90 -91 -92 0\n-10 -13 -14 -16 -32 -41 -46 -53 -58 -65 -80 -89 -90 -92 0\n-3 -7 -8 -15 -32 -42 -46 -57 -66 -72 -74 -90 -91 -92 0\n-8 -10 -11 -13 -32 -41 -46 -58 -65 -72 -80 -89 -90 -92 0\n-5 -10 -11 -17 -28 -33 -41 -58 -65 -72 -80 -89 -90 -92 0\n-10 -14 -17 -20 -32 -40 -42 -57 -59 -63 -74 -83 -86 -88 0\n-10 -13 -14 -18 -32 -40 -42 -57 -59 -63 -83 -84 -86 -88 0\n-10 -13 -14 -18 -32 -36 -42 -46 -57 -59 -83 -86 -88 -91 0\n-3 -9 -10 -14 -32 -42 -46 -57 -59 -74 -83 -86 -88 -91 0\n-5 -10 -12 -14 -32 -36 -42 -54 -59 -77 -83 -86 -88 -91 0\n-3 -9 -10 -14 -32 -42 -45 -54 -59 -77 -83 -86 -88 -91 0\n-4 -7 -12 -17 -26 -33 -40 -63 -67 -78 -83 -86 -88 -89 0\n-2 -3 -10 -19 -31 -42 -54 -59 -65 -78 -83 -84 -86 -88 0\n-3 -4 -7 -19 -26 -33 -46 -65 -67 -78 -83 -86 -88 -89 0\n-3 -4 -7 -19 -31 -33 -54 -65 -67 -78 -83 -84 -86 -88 0\n-2 -3 -10 -19 -26 -42 -46 -59 -65 -78 -83 -86 -88 -89 0\n-4 -7 -12 -17 -31 -33 -36 -54 -67 -78 -83 -86 -88 -91 0\n-11 -15 -16 -19 -26 -33 -41 -46 -51 -65 -78 -89 -90 -92 0\n-3 -8 -9 -14 -32 -42 -46 -51 -57 -74 -83 -90 -91 -92 0\n-11 -16 -17 -20 -31 -33 -41 -51 -54 -65 -78 -80 -90 -92 0\n-11 -15 -16 -19 -31 -33 -41 -51 -54 -65 -78 -84 -90 -92 0\n-5 -11 -12 -16 -26 -33 -41 -51 -63 -78 -82 -89 -90 -92 0\n-3 -8 -9 -14 -32 -42 -45 -51 -54 -77 -83 -90 -91 -92 0\n-4 -11 -12 -17 -26 -33 -40 -51 -63 -78 -83 -89 -90 -92 0\n-2 -3 -8 -19 -31 -42 -51 -54 -65 -78 -83 -84 -90 -92 0\n-3 -4 -11 -19 -26 -33 -46 -51 -65 -78 -83 -89 -90 -92 0\n-3 -4 -11 -19 -31 -33 -51 -54 -65 -78 -83 -84 -90 -92 0\n-2 -3 -8 -19 -26 -42 -46 -51 -65 -78 -83 -89 -90 -92 0\n-4 -11 -12 -17 -31 -33 -36 -51 -54 -78 -83 -90 -91 -92 0\n-11 -14 -16 -19 -28 -33 -41 -45 -58 -66 -82 -86 -88 -89 0\n-11 -14 -16 -19 -31 -33 -41 -58 -66 -70 -74 -82 -86 -88 0\n-3 -8 -14 -18 -32 -42 -45 -58 -66 -77 -83 -86 -88 -91 0\n-1 -3 -11 -19 -33 -39 -45 -58 -66 -78 -82 -86 -88 -89 0\n-3 -8 -12 -14 -32 -42 -46 -58 -66 -74 -83 -86 -88 -91 0\n-3 -8 -12 -17 -30 -31 -42 -58 -66 -74 -83 -86 -88 -91 0\n-11 -16 -18 -19 -31 -33 -41 -58 -66 -70 -78 -82 -86 -88 0\n-11 -16 -17 -18 -31 -33 -41 -58 -66 -70 -78 -80 -86 -88 0\n-11 -14 -16 -19 -28 -33 -41 -45 -58 -66 -82 -85 -87 -89 0\n-11 -14 -16 -19 -31 -33 -41 -58 -66 -70 -74 -82 -85 -87 0\n-3 -8 -14 -18 -32 -42 -45 -58 -66 -77 -83 -85 -87 -91 0\n-1 -3 -11 -19 -33 -39 -45 -58 -66 -78 -82 -85 -87 -89 0\n-3 -8 -12 -14 -32 -42 -46 -58 -66 -74 -83 -85 -87 -91 0\n-3 -8 -12 -17 -30 -31 -42 -58 -66 -74 -83 -85 -87 -91 0\n-11 -16 -18 -19 -31 -33 -41 -58 -66 -70 -78 -82 -85 -87 0\n-11 -16 -17 -18 -31 -33 -41 -58 -66 -70 -78 -80 -85 -87 0\n-11 -18 -19 -20 -28 -33 -41 -45 -58 -66 -72 -82 -90 -92 0\n-11 -13 -18 -19 -31 -33 -41 -58 -66 -70 -72 -82 -90 -92 0\n-4 -14 -18 -19 -32 -40 -53 -58 -66 -70 -77 -83 -90 -92 0\n-11 -16 -18 -19 -31 -33 -41 -58 -66 -70 -78 -82 -90 -92 0\n-12 -16 -19 -20 -30 -31 -41 -53 -58 -66 -74 -82 -90 -92 0\n-11 -12 -19 -20 -31 -33 -41 -58 -66 -72 -74 -82 -90 -92 0\n-4 -14 -17 -19 -32 -40 -53 -58 -66 -70 -74 -83 -90 -92 0\n-11 -16 -17 -18 -31 -33 -41 -58 -66 -70 -78 -80 -90 -92 0\n-5 -14 -16 -19 -32 -41 -53 -58 -66 -70 -74 -82 -90 -92 0\n-4 -14 -16 -18 -32 -40 -53 -58 -66 -70 -77 -80 -90 -92 0\n-11 -14 -16 -19 -31 -33 -41 -58 -66 -70 -74 -82 -90 -92 0\n-11 -15 -17 -19 -31 -33 -41 -58 -66 -70 -72 -74 -90 -92 0\n-11 -13 -17 -18 -31 -33 -41 -58 -66 -70 -72 -80 -90 -92 0\n-3 -4 -11 -19 -31 -33 -58 -66 -70 -72 -74 -82 -90 -92 0\n-3 -5 -8 -19 -32 -42 -58 -66 -70 -72 -74 -82 -90 -92 0\n-2 -3 -8 -19 -31 -42 -58 -66 -70 -72 -74 -82 -90 -92 0\n-3 -5 -8 -18 -32 -42 -58 -66 -70 -72 -77 -80 -90 -92 0\n-5 -8 -11 -19 -32 -41 -58 -66 -70 -72 -74 -82 -90 -92 0\n-4 -8 -11 -18 -32 -40 -58 -66 -70 -72 -77 -80 -90 -92 0\n-5 -11 -12 -19 -28 -33 -41 -58 -66 -72 -82 -89 -90 -92 0\n-11 -15 -17 -18 -28 -33 -41 -45 -58 -66 -72 -90 -91 -92 0\n-11 -15 -17 -19 -28 -33 -41 -45 -58 -66 -72 -89 -90 -92 0\n-1 -3 -4 -18 -30 -45 -53 -58 -66 -77 -83 -90 -91 -92 0\n-1 -3 -11 -19 -33 -39 -45 -58 -66 -78 -82 -89 -90 -92 0\n-3 -13 -14 -19 -32 -39 -45 -53 -58 -66 -82 -89 -90 -92 0\n-3 -4 -11 -19 -28 -33 -45 -58 -66 -72 -82 -89 -90 -92 0\n-3 -8 -13 -19 -32 -42 -45 -58 -66 -72 -82 -89 -90 -92 0\n-2 -3 -8 -19 -28 -42 -45 -58 -66 -72 -82 -89 -90 -92 0\n-3 -8 -14 -18 -32 -42 -45 -58 -66 -77 -83 -90 -91 -92 0\n-11 -14 -16 -19 -28 -33 -41 -45 -58 -66 -82 -89 -90 -92 0\n-3 -4 -14 -18 -32 -45 -53 -58 -66 -77 -83 -90 -91 -92 0\n-3 -14 -15 -18 -32 -39 -45 -53 -58 -66 -77 -90 -91 -92 0\n-4 -14 -16 -18 -32 -38 -45 -53 -58 -66 -77 -90 -91 -92 0\n-14 -15 -16 -18 -32 -41 -45 -53 -58 -66 -77 -90 -91 -92 0\n-3 -8 -15 -18 -32 -42 -45 -58 -66 -72 -77 -90 -91 -92 0\n-8 -11 -15 -18 -32 -41 -45 -58 -66 -72 -77 -90 -91 -92 0\n-4 -8 -11 -18 -32 -38 -45 -58 -66 -72 -77 -90 -91 -92 0\n-5 -11 -12 -17 -28 -33 -41 -58 -66 -72 -80 -89 -90 -92 0\n-3 -4 -12 -17 -30 -31 -53 -58 -66 -74 -83 -90 -91 -92 0\n-3 -8 -12 -17 -30 -31 -42 -58 -66 -74 -83 -90 -91 -92 0\n-12 -15 -16 -17 -30 -31 -41 -53 -58 -66 -74 -90 -91 -92 0\n-4 -11 -12 -17 -28 -33 -40 -58 -66 -72 -80 -89 -90 -92 0\n-11 -12 -15 -17 -31 -33 -41 -58 -66 -72 -74 -90 -91 -92 0\n-4 -11 -12 -17 -31 -33 -38 -58 -66 -72 -74 -90 -91 -92 0\n-3 -4 -12 -14 -32 -46 -53 -58 -66 -74 -83 -90 -91 -92 0\n-3 -8 -12 -14 -32 -42 -46 -58 -66 -74 -83 -90 -91 -92 0\n-12 -14 -15 -16 -32 -41 -46 -53 -58 -66 -74 -90 -91 -92 0\n-3 -8 -12 -15 -32 -42 -46 -58 -66 -72 -74 -90 -91 -92 0\n-3 -8 -12 -13 -32 -42 -46 -58 -66 -72 -80 -89 -90 -92 0\n-8 -11 -12 -15 -32 -41 -46 -58 -66 -72 -74 -90 -91 -92 0\n-11 -14 -15 -16 -32 -41 -46 -57 -59 -66 -74 -86 -88 -91 0\n-11 -14 -15 -16 -32 -41 -45 -54 -59 -66 -77 -86 -88 -91 0\n-3 -4 -11 -14 -32 -46 -57 -59 -66 -74 -83 -86 -88 -91 0\n-3 -4 -11 -14 -32 -45 -54 -59 -66 -77 -83 -86 -88 -91 0\n-5 -14 -16 -17 -32 -38 -42 -57 -59 -66 -74 -86 -88 -91 0\n-3 -14 -15 -16 -32 -42 -46 -57 -59 -66 -74 -86 -88 -91 0\n-9 -14 -16 -19 -28 -33 -41 -45 -58 -67 -82 -86 -88 -89 0\n-3 -14 -15 -16 -32 -42 -45 -54 -59 -66 -77 -86 -88 -91 0\n-12 -14 -16 -20 -32 -40 -42 -54 -59 -66 -77 -80 -86 -88 0\n-9 -14 -16 -19 -31 -33 -41 -58 -67 -70 -74 -82 -86 -88 0\n-3 -14 -19 -20 -32 -42 -46 -57 -59 -66 -74 -83 -86 -88 0\n-3 -14 -19 -20 -32 -42 -45 -54 -59 -66 -77 -83 -86 -88 0\n-2 -3 -12 -19 -26 -42 -46 -59 -66 -78 -83 -86 -88 -89 0\n-2 -3 -12 -19 -31 -42 -54 -59 -66 -78 -83 -84 -86 -88 0\n-3 -6 -14 -18 -32 -42 -45 -59 -66 -77 -83 -86 -88 -91 0\n-1 -3 -9 -19 -33 -39 -45 -58 -67 -78 -82 -86 -88 -89 0\n-2 -3 -12 -18 -26 -42 -46 -59 -66 -78 -83 -86 -88 -91 0\n-3 -5 -12 -18 -26 -30 -42 -59 -66 -77 -83 -86 -88 -91 0\n-3 -13 -14 -18 -32 -42 -46 -57 -59 -66 -83 -86 -88 -91 0\n-1 -3 -4 -19 -33 -46 -58 -65 -67 -78 -83 -86 -88 -89 0\n-2 -3 -12 -17 -31 -42 -54 -59 -66 -78 -83 -86 -88 -91 0\n-3 -5 -12 -14 -32 -42 -54 -59 -66 -77 -83 -86 -88 -91 0\n-3 -13 -14 -17 -32 -42 -45 -54 -59 -66 -83 -86 -88 -91 0\n-1 -3 -4 -17 -33 -45 -58 -63 -67 -78 -83 -86 -88 -89 0\n-1 -3 -4 -16 -33 -45 -58 -63 -67 -78 -82 -86 -88 -89 0\n-3 -6 -12 -14 -32 -42 -46 -59 -66 -74 -83 -86 -88 -91 0\n-3 -6 -12 -17 -30 -31 -42 -59 -66 -74 -83 -86 -88 -91 0\n-3 -5 -14 -17 -32 -42 -57 -59 -66 -74 -83 -86 -88 -91 0\n-1 -3 -4 -16 -33 -46 -58 -65 -67 -78 -80 -86 -88 -89 0\n-1 -3 -5 -17 -33 -39 -58 -65 -67 -78 -80 -86 -88 -89 0\n-4 -12 -17 -18 -31 -33 -36 -58 -67 -78 -83 -86 -88 -91 0\n-12 -18 -19 -20 -31 -33 -36 -39 -58 -67 -78 -82 -86 -88 0\n-12 -15 -17 -18 -31 -33 -36 -39 -58 -67 -78 -86 -88 -91 0\n-12 -16 -18 -20 -31 -33 -41 -58 -63 -67 -78 -82 -86 -88 0\n-12 -15 -16 -18 -31 -33 -41 -58 -63 -67 -78 -84 -86 -88 0\n-3 -4 -12 -18 -31 -33 -58 -63 -67 -78 -83 -84 -86 -88 0\n-3 -4 -18 -19 -31 -33 -58 -65 -67 -78 -83 -84 -86 -88 0\n-3 -15 -18 -19 -31 -33 -39 -58 -65 -67 -78 -84 -86 -88 0\n-4 -16 -18 -19 -31 -33 -38 -58 -65 -67 -78 -84 -86 -88 0\n-15 -16 -18 -19 -31 -33 -41 -58 -65 -67 -78 -84 -86 -88 0\n-16 -17 -18 -20 -31 -33 -41 -58 -65 -67 -78 -80 -86 -88 0\n-3 -17 -18 -20 -31 -33 -39 -58 -65 -67 -78 -80 -86 -88 0\n-9 -16 -18 -19 -31 -33 -41 -58 -67 -70 -78 -82 -86 -88 0\n-9 -16 -17 -18 -31 -33 -41 -58 -67 -70 -78 -80 -86 -88 0\n-4 -17 -18 -19 -31 -33 -36 -58 -67 -70 -78 -83 -86 -88 0\n-4 -16 -18 -19 -31 -33 -36 -58 -67 -70 -78 -82 -86 -88 0\n7 8 10 11 24 33 42 51 53 58 59 66 67 0\n7 8 24 33 51 53 58 59 73 86 87 88 90 0\n7 10 51 58 59 66 67 86 87 90 92 0\n8 11 33 42 53 59 67 73 87 88 90 92 0\n"
  "1199 -162 0 691 685 0\n1200 -138 0 691 690 0\n1201 181 0 798 792 0\n1202 191 0 798 796 0\n1203 178 0 1201 757 0\n1204 188 0 1202 787 0\n1205 -212 0 878 877 0\n1206 210 0 853 854 851 852 844 845 849 810 804 805 802 814 385 415 384 414 387 417 416 1198 0\n1207 -220 0 1206 878 875 0\n1208 -218 0 1207 871 0\n1209 -214 0 1207 874 0\n1210 -216 0 1208 866 0\n1211 -205 203 0 1210 829 828 864 836 838 520 526 841 0\n1212 -215 0 1208 868 828 829 831 832 834 528 530 533 1211 842 843 861 519 525 835 0\n1213 -205 0 1212 862 0\n1214 -204 0 1212 863 0\n1215 -60 0 1213 842 0\n1216 -68 0 1213 843 0\n1217 -55 0 1214 836 0\n1218 -61 0 1214 837 0\n1219 -62 0 1214 838 0\n1220 -64 0 1214 839 0\n1221 -69 0 1214 840 0\n1222 -29 0 1217 1215 518 0\n1223 -47 0 1218 527 0\n1224 -37 0 1219 1216 524 0\n1225 -56 0 1220 532 0\n1226 -48 0 1221 529 0\n1227 209 -217 0 1207 1212 1226 1223 1225 1224 1222 865 873 859 820 858 824 851 852 848 849 808 816 812 514 508 827 0\n1228 206 0 844 845 803 805 800 801 802 531 410 411 373 376 409 412 375 1197 0\n1229 202 34 -219 0 1228 878 876 855 851 848 818 817 1227 869 825 826 857 516 522 819 0\n1230 43 -219 0 1228 878 1209 876 855 1227 867 830 851 848 818 817 816 512 1229 860 821 822 517 523 823 0\n1231 -43 44 25 0 1209 513 824 820 860 0\n1232 -219 0 878 1228 876 855 851 1227 848 867 816 830 1230 1231 0\n1233 -217 0 1232 870 0\n1234 -213 0 1232 872 0\n1235 -203 0 1233 867 0\n1236 -202 0 1234 858 0\n1237 -201 0 1234 859 0\n1238 -44 0 1235 830 0\n1239 -52 0 1235 833 0\n1240 -43 0 1236 824 0\n1241 -76 0 1236 825 0\n1242 -81 0 1236 826 0\n1243 -34 0 1237 820 0\n1244 -75 0 1237 821 0\n1245 -79 0 1237 822 0\n1246 -25 0 1238 1240 1243 511 0\n1247 -27 0 1241 1244 515 0\n1248 -35 0 1242 1245 521 0\n1249 -200 0 1246 1247 1248 815 0\n1250 131 59 58 51 -166 0 1218 1225 609 613 606 596 553 551 287 381 365 367 699 0\n1251 -39 -171 0 66 90 117 143 722 0\n1252 -46 -72 -180 -193 0 185 161 157 156 750 741 747 790 779 769 786 765 62 65 67 68 214 703 16 23 699 55 717 171 191 727 0\n1253 -45 41 38 -170 0 59 60 717 0\n1254 -54 -72 -180 -193 0 185 161 157 156 750 741 747 790 779 771 769 786 765 763 86 87 89 96 173 234 703 19 23 712 699 200 217 55 1253 727 191 246 717 731 123 0\n1255 -63 -72 -180 -193 0 185 161 157 156 750 741 747 790 779 771 786 765 113 115 116 126 243 703 731 23 197 699 717 55 0\n1256 -72 -180 -193 0 750 741 790 779 771 776 786 763 157 185 1252 1254 1255 722 140 147 149 236 245 703 731 19 200 712 0\n1257 -70 82 -173 0 149 245 731 0\n1258 -65 -83 -170 0 205 203 122 123 717 0\n1259 -83 -193 0 790 779 771 769 786 765 203 205 208 209 1253 1258 731 242 248 717 25 171 727 0\n1260 38 41 -91 -193 0 248 246 242 790 779 769 786 765 1253 717 25 171 727 0\n1261 -38 -91 -171 0 245 243 65 89 722 0\n1262 -32 -66 -74 -7 -57 -46 -72 -41 -15 -91 0 1218 1221 1220 1225 1239 228 412 161 159 326 376 473 451 288 899 0\n1263 -46 -72 -91 -193 209 0 1218 1221 1239 1220 1225 1246 1201 1248 228 412 161 159 790 776 1261 1260 326 1256 752 376 473 451 185 160 157 156 55 1259 471 249 248 246 779 769 786 763 851 849 812 852 807 62 64 68 177 712 93 103 349 727 692 735 736 696 754 1262 703 266 741 894 746 699 0\n1264 167 -77 -66 -45 -7 -54 -72 -41 -15 -91 0 1218 1225 1221 1239 1220 1201 228 376 160 102 692 736 754 58 412 161 159 326 473 451 156 55 706 741 270 746 888 699 0\n1265 -72 -91 -193 209 0 1218 1221 1201 1220 1247 1225 1239 790 776 1261 1260 1259 471 249 248 246 245 243 779 769 786 763 852 807 157 159 160 161 185 228 451 473 1256 376 412 752 326 1263 722 86 87 96 102 173 348 692 727 735 58 696 712 1264 703 288 893 0\n1266 -51 -165 0 131 136 696 0\n1267 -175 -32 -14 -77 -45 -54 -16 -41 -15 -91 73 0 102 55 736 737 1266 692 138 376 382 387 696 1150 0\n1268 -32 -14 -77 -45 -54 177 -16 -41 -15 -91 73 0 1201 102 750 752 44 55 23 1267 754 746 699 83 109 137 367 386 416 692 891 735 696 0\n1269 -54 -91 -193 209 0 1221 1243 1224 1245 1246 691 1203 1201 1218 1239 1265 851 849 813 790 776 1251 852 808 1259 1261 471 454 566 654 667 708 743 1260 44 565 249 248 246 779 769 786 763 814 86 87 88 96 102 173 727 58 712 187 431 563 639 641 647 680 687 624 592 1268 703 270 739 539 748 745 573 574 754 588 541 737 621 290 1266 1250 0\n1270 72 -74 -57 -46 -41 -91 -179 58 -165 0 1242 1222 186 63 62 45 510 246 247 321 205 55 48 44 43 748 708 329 430 743 739 746 703 23 699 137 367 386 416 696 897 0\n1271 -72 -193 -41 -91 0 1239 1249 45 510 43 507 42 505 811 847 231 1265 806 850 0\n1272 -74 -193 -41 -91 -179 58 -165 0 1271 790 776 786 763 249 245 243 173 179 722 64 1270 712 0\n1273 -46 57 72 74 -41 -91 58 51 0 1242 1240 798 1199 45 510 329 566 654 205 48 708 743 750 246 247 321 565 637 640 55 249 244 64 91 177 337 495 712 560 568 763 661 786 668 793 684 755 652 736 635 692 558 382 0\n1274 -59 -166 -41 0 55 44 107 109 699 0\n1275 -179 57 72 74 -41 -91 58 51 0 1242 798 1246 1273 205 48 708 743 750 45 510 329 42 505 246 247 321 43 249 248 245 243 748 746 739 1274 692 736 755 793 786 790 763 776 779 722 769 86 87 88 727 58 712 187 431 703 1268 0\n1276 57 72 74 -41 -91 58 51 0 1239 1249 1201 798 45 510 43 507 42 505 811 847 245 243 1273 1275 758 754 793 736 790 692 776 230 722 806 1269 850 0\n1277 72 74 -41 -91 58 51 0 798 205 48 248 246 708 743 750 1276 93 95 727 769 779 790 793 758 755 746 736 1274 692 0\n1278 -72 -41 -91 58 51 0 1242 1225 1218 1220 1221 798 691 1245 246 247 321 565 637 640 45 510 55 44 249 248 157 161 185 228 451 473 1271 376 378 419 793 692 551 558 736 596 634 755 613 649 747 750 617 699 741 686 23 681 703 432 439 567 568 653 661 668 0\n1279 -91 -165 175 51 -41 58 0 1201 798 754 205 48 1278 708 1277 743 1272 750 793 755 0\n1280 -30 -171 54 0 63 114 141 722 0\n1281 168 -74 91 -165 175 -41 0 1201 798 237 186 179 173 170 754 748 55 44 743 739 750 746 755 793 786 790 763 776 779 771 1280 703 19 23 712 699 125 147 137 731 696 198 132 722 0\n1282 -165 175 -41 83 91 66 39 -74 0 1225 1218 696 1281 241 708 451 0\n1283 174 83 39 0 1201 798 752 753 750 793 743 1256 708 0\n1284 164 -41 83 91 66 39 -74 0 1283 736 735 1282 0\n1285 -59 -41 83 66 39 0 1225 1218 1201 138 240 1274 696 451 737 708 754 743 746 0\n1286 -41 58 83 91 66 39 -32 -74 0 1201 23 14 55 1284 1285 692 83 160 1266 699 708 737 743 754 746 0\n1287 41 -63 -82 83 165 -164 39 0 798 1220 1221 1248 1225 1239 1218 115 114 113 219 201 200 197 196 737 756 794 782 698 323 717 765 762 786 784 793 779 755 769 747 750 741 743 708 155 156 159 160 161 185 228 451 473 392 703 376 16 19 23 692 288 699 103 712 237 443 727 1046 0\n1288 -32 -11 -58 -10 -72 59 -41 -63 -82 175 0 1221 1220 1225 1239 798 1218 103 98 473 451 185 161 159 55 44 113 219 201 200 19 23 288 699 747 755 793 786 790 763 779 712 769 237 443 727 1051 0\n1289 74 -172 -169 -33 32 -11 -58 -10 -72 -41 -63 -82 0 1218 1225 1221 1220 1240 1223 1224 103 98 473 451 185 113 219 201 200 436 727 58 265 712 892 0\n1290 -72 59 -41 -63 -82 165 -164 0 1201 1225 1218 1221 1220 1239 798 1219 1240 1248 55 44 42 148 114 113 247 200 199 737 754 698 159 160 161 185 451 473 392 692 326 103 1288 703 741 750 746 755 699 793 786 790 763 779 769 1289 172 237 493 355 712 1044 0\n1291 -74 57 -169 -167 30 28 77 0 186 237 703 712 19 0\n1292 -32 -89 -45 74 -10 -58 -166 72 -41 -63 -82 0 1241 45 510 329 55 44 200 23 292 275 699 386 416 1049 0\n1293 -53 -78 32 -89 -45 -10 -58 -16 -41 -63 -82 0 1224 1223 1218 1225 113 265 114 289 386 416 889 0\n1294 -90 -33 -11 -1 -78 -89 -45 -10 -58 -16 -41 -63 -82 0 536 890 0\n1295 86 -33 -11 -1 -78 -89 -45 -10 -58 -16 -41 -63 -82 0 1225 1246 1294 42 505 119 487 375 882 0\n1296 -33 -11 -82 -1 -78 -89 -45 -10 -58 -16 -41 -63 0 1295 534 880 0\n1297 -58 -172 -169 -166 -167 72 -41 -63 -82 165 0 1223 1224 1220 1239 45 510 329 55 44 114 113 219 201 200 698 697 98 100 103 369 1291 727 58 712 1292 703 265 1293 326 699 1296 0\n1298 -45 -78 -33 -16 -51 -41 -89 58 -63 -82 0 1219 1223 1224 23 410 55 406 374 120 113 353 265 918 0\n1299 165 -164 -89 58 -63 -82 0 1201 798 1247 1241 237 235 233 132 117 114 113 219 209 201 737 1287 754 44 45 55 1285 748 510 1290 692 708 329 83 374 406 410 743 739 750 746 755 699 793 23 790 703 779 769 1298 727 397 345 1075 0\n1300 -164 -89 58 -63 -82 0 132 1299 1266 696 692 138 0\n1301 45 -172 -41 -78 -33 -7 -67 -89 -63 -82 0 1218 1225 1243 1247 1241 412 227 117 112 241 451 460 534 237 235 233 219 201 727 397 345 905 0\n1302 -89 58 -63 -82 0 1201 1225 1218 1243 798 1219 1223 1224 209 117 1283 132 120 115 114 113 112 197 196 1300 736 735 754 696 748 135 137 241 372 412 451 223 227 534 708 460 743 739 750 746 755 699 793 23 786 790 703 765 779 717 769 1301 353 265 906 0\n1303 -165 58 -63 -82 0 1244 1225 1218 1243 1201 1215 691 1216 1219 1241 219 1302 499 570 656 148 132 120 117 114 113 112 209 199 1266 696 135 137 138 241 372 412 692 451 551 223 227 736 708 460 596 754 743 566 613 748 746 654 617 739 699 686 23 703 442 568 662 669 674 678 687 648 621 633 588 560 573 335 352 539 278 0\n1304 58 -63 -82 0 1244 1201 1243 1215 1199 691 1216 1219 1241 209 117 1283 148 132 120 114 113 112 219 199 1302 499 570 656 1303 737 735 1287 754 42 44 55 1285 1290 748 505 692 708 460 739 83 406 743 566 558 746 654 634 699 648 23 703 442 568 662 669 678 682 686 651 620 635 588 560 573 335 352 539 278 0\n1305 165 -63 -82 0 1201 798 1304 694 110 117 209 737 1287 754 1290 748 708 739 743 750 746 755 793 786 790 763 779 1297 769 0\n1306 172 -41 -78 -33 89 -63 -82 0 1243 1218 1225 798 1244 1215 1219 1240 1248 120 442 219 499 209 117 132 1305 696 241 451 708 743 750 760 794 1304 97 505 112 460 412 534 103 148 200 199 728 769 355 779 1182 784 712 763 0\n1307 -41 -78 -33 89 -63 -82 0 1218 1225 1243 1244 1215 1223 1224 120 442 186 23 219 499 1304 97 505 117 112 132 1305 696 241 451 460 412 534 98 113 201 1306 727 265 1002 0\n1308 -33 -167 89 -63 -82 0 1218 1225 1243 1244 1215 691 1221 1239 219 499 570 656 1304 97 505 117 112 132 1305 696 241 451 460 566 654 412 223 120 115 114 113 23 703 442 568 662 669 674 687 624 586 1307 323 328 543 545 582 577 0\n1309 -167 89 -63 -82 0 1218 1225 798 209 117 132 1305 696 241 451 708 743 412 223 137 135 1304 103 98 114 113 219 201 200 1308 699 746 758 793 786 790 763 779 1291 712 769 58 727 0\n1310 89 -63 -82 0 1218 1225 1243 1244 1226 1223 1203 798 1216 1304 97 505 117 112 132 1305 696 241 451 460 209 708 412 534 223 137 135 103 98 148 115 114 219 201 200 199 197 196 499 1309 707 739 445 748 745 758 699 793 786 790 763 765 779 712 717 769 58 335 727 999 0\n1311 167 -63 -82 0 1225 1243 1215 1226 1223 1218 1203 798 1310 237 233 1304 97 505 117 112 132 1305 696 241 451 460 209 708 412 534 223 137 135 98 115 114 113 219 201 197 196 706 707 739 272 445 443 748 745 758 699 793 786 790 765 779 717 769 998 727 0\n1312 -172 -166 -63 -82 0 1218 1225 1243 1246 1247 1222 799 1221 1239 1311 114 113 132 1305 696 137 135 412 223 699 23 703 1304 694 738 742 749 759 795 1310 233 97 112 98 257 716 237 505 117 241 451 460 534 725 115 733 219 201 772 727 780 791 766 721 323 328 1173 0\n1313 -166 -63 -82 0 1243 1218 1225 798 1222 1247 1246 1219 1240 1248 1241 1311 1310 233 209 117 132 1305 696 241 451 708 743 750 760 794 1304 97 505 112 460 412 534 223 137 135 98 148 115 114 113 199 197 196 699 23 257 703 1312 728 769 355 345 779 1012 784 717 765 0\n1314 -78 -63 -82 0 1243 1218 1225 798 1241 1304 98 201 1310 237 219 209 117 132 1305 696 241 451 708 743 1313 746 758 793 790 779 769 727 196 115 197 786 765 717 137 134 700 368 233 97 505 112 460 412 534 223 510 295 278 994 0\n1315 -63 -82 0 1225 1243 798 1226 1223 1218 219 209 201 197 196 112 113 114 115 117 132 1304 97 98 505 1305 696 134 137 241 412 451 534 708 460 743 1310 237 1311 1313 700 746 368 758 793 786 790 765 779 717 769 727 1314 445 703 443 992 0\n1316 -67 -41 33 -179 83 0 1225 1218 55 48 44 137 241 699 451 746 708 743 0\n1317 28 -58 -8 -11 -66 -72 -167 78 -41 -45 -89 -82 0 1225 1221 1220 1218 473 451 157 1315 469 443 703 976 0\n1318 166 78 -41 -45 33 -89 -82 0 798 1225 1218 1220 1221 1247 209 234 1315 198 236 722 776 790 793 758 1316 45 510 55 48 44 56 469 702 747 746 755 741 743 736 737 708 1266 696 228 451 473 408 376 389 692 1317 254 977 0\n1319 -28 -166 -41 -45 33 -89 -82 0 1221 1243 798 1247 1244 209 234 1315 198 236 722 776 790 793 758 1316 48 55 44 699 161 708 743 750 755 737 696 1274 83 736 692 150 43 460 416 386 45 56 469 254 427 973 0\n1320 -2 28 -167 78 0 5 11 703 0\n1321 30 28 -66 -58 -53 78 -41 -45 -89 -82 0 1221 1243 798 1218 1226 1223 443 234 1315 198 236 722 776 790 793 758 748 209 48 161 708 739 150 43 460 416 386 469 445 703 974 0\n1322 78 -41 -45 33 -89 -82 0 1221 798 1243 1218 1247 209 234 1315 198 236 722 776 790 793 758 1316 55 48 45 44 43 150 57 56 233 469 1318 1274 699 83 161 386 416 708 460 743 750 755 736 737 692 696 1319 443 1321 255 972 0\n1323 -41 -45 33 -89 -82 0 1221 798 1226 1241 57 234 1315 198 236 722 776 790 793 758 233 469 209 44 45 48 55 510 1316 1322 185 448 295 278 708 743 750 746 755 1274 699 736 737 83 386 416 692 696 971 0\n1324 -78 -45 33 -89 -82 0 1221 798 1241 234 1315 198 236 722 776 196 59 197 1323 717 765 784 794 760 750 743 756 737 1266 747 736 323 57 233 469 209 183 185 278 708 32 54 282 699 109 137 386 416 692 696 963 0\n1325 -53 78 -168 -167 -165 -164 -3 -45 -89 -82 0 1221 1218 1266 1315 469 209 109 137 161 386 416 692 696 708 33 34 447 443 703 1123 0\n1326 -39 53 -166 33 0 32 54 699 0\n1327 -32 -8 -66 -58 -90 -42 -72 -3 -45 -89 -82 0 1221 1241 536 237 1315 469 200 275 1125 0\n1328 -90 -45 33 -89 -82 0 1221 798 1205 59 1323 323 234 1315 198 236 722 776 196 197 717 765 784 794 756 736 737 760 750 741 743 1324 1325 747 209 1326 708 156 699 157 1266 469 240 241 536 802 692 696 805 846 856 852 809 368 1327 703 294 1126 0\n1329 -45 33 -89 -82 0 798 1225 1218 234 1315 198 236 722 776 209 197 196 59 1323 323 717 765 784 794 756 760 736 737 747 750 741 743 1324 1325 1326 708 1328 451 0\n1330 -72 -165 53 -104 -5 33 -82 0 1221 1225 1218 691 1226 1238 1222 1247 1220 1239 1315 469 569 657 659 664 633 648 676 688 547 576 580 585 196 159 168 228 451 389 412 553 696 606 128 609 621 625 687 586 680 582 651 543 635 309 558 326 0\n1331 -90 3 -165 53 33 -89 -82 0 798 1242 1241 1239 1221 1216 1224 1248 1243 233 1329 345 199 423 560 1330 234 1315 198 236 722 776 790 793 758 209 197 196 241 490 489 696 504 506 128 318 298 303 48 699 708 746 743 0\n1332 -41 72 53 33 -179 83 0 44 48 55 708 699 743 746 0\n1333 -193 41 -82 0 219 201 197 196 786 790 765 779 717 1253 769 25 171 727 0\n1334 -67 -166 53 33 0 135 412 699 223 0\n1335 40 -66 -12 120 -42 33 0 1247 1239 1215 1221 1216 1246 129 506 55 585 581 543 128 314 127 580 576 547 588 572 541 52 51 334 318 256 30 0\n1336 -30 -171 0 88 1280 0\n1337 -100 54 57 30 22 66 135 -42 33 0 1225 1247 1217 1246 1222 619 611 52 51 606 607 609 614 599 621 597 556 588 549 405 572 347 541 253 0\n1338 54 57 30 22 21 66 135 -42 33 0 1239 1217 1247 1246 1222 507 619 52 51 1337 553 366 381 405 556 599 603 609 614 621 597 588 549 572 350 541 253 0\n1339 -9 -40 129 -42 33 0 1239 1220 1219 1248 1243 307 507 305 605 135 70 555 601 602 607 556 553 390 366 0\n1340 -17 -14 -32 -57 -63 70 -83 -10 -59 -172 -40 -42 0 1216 1215 235 93 208 165 387 376 242 60 210 476 727 1059 0\n1341 135 9 8 -40 66 -42 33 0 798 1247 1221 1239 1218 1225 1241 1223 1224 1219 315 120 113 39 399 366 405 556 599 603 609 135 696 737 123 197 242 731 771 779 790 793 755 750 743 54 165 82 389 451 708 381 387 376 756 794 788 774 1336 777 767 307 305 51 621 1338 588 178 572 541 295 290 453 1340 342 437 494 1060 0\n1342 2 -113 30 22 21 -42 33 0 1222 1247 1246 52 51 540 251 571 538 0\n1343 -57 -78 -2 -63 -83 -10 -59 -172 -40 -42 0 1222 1247 1246 1215 186 120 113 208 165 387 376 307 305 60 38 52 93 235 252 442 727 910 0\n1344 132 8 -40 66 -42 33 0 1239 1218 1225 798 1221 1215 1217 1247 1246 1216 366 405 556 599 603 135 696 737 123 197 242 731 771 779 790 793 755 750 743 54 165 82 389 451 708 381 387 376 741 756 794 784 763 788 774 1336 36 542 50 544 37 546 575 579 777 767 307 507 305 67 39 38 611 614 1339 597 399 315 549 113 120 1341 618 584 1342 1320 1343 187 336 350 712 912 481 0\n1345 -63 -83 -10 -59 175 -2 -40 -42 0 798 1215 1216 208 165 387 376 123 197 242 731 756 794 788 777 767 771 779 784 763 790 793 755 750 741 67 60 38 113 148 1320 186 187 1343 712 336 239 481 727 912 0\n1346 8 66 -2 -40 -42 33 0 798 1225 1218 691 1221 1220 1219 1243 1223 1224 1245 1217 1238 1247 123 197 242 731 771 779 790 793 135 696 737 755 750 743 541 572 588 67 60 165 82 54 366 381 389 1344 405 376 451 622 708 688 208 673 665 1345 315 497 569 657 659 662 664 668 568 676 653 648 567 633 434 560 492 359 395 0\n1347 -70 57 -169 -167 -2 31 0 140 236 1320 712 187 0\n1348 -58 175 -2 -40 0 798 123 197 242 731 756 794 788 777 767 771 779 784 763 774 790 793 755 750 741 67 60 38 98 102 103 1347 722 113 194 1320 186 187 727 712 239 0\n1349 -51 58 -89 -78 -12 -63 -2 -40 0 798 1216 691 1219 1240 1248 541 572 588 560 633 648 197 67 481 567 653 667 676 688 622 185 120 117 20 1 123 242 731 771 779 790 793 83 374 410 1266 366 737 553 755 606 747 750 614 699 743 597 708 549 924 351 0\n1350 164 66 33 -182 0 753 736 735 755 696 747 137 1334 0\n1351 -59 -63 -2 0 798 126 1315 243 731 771 779 790 793 132 116 115 20 1 105 109 138 696 737 756 755 794 747 784 699 1274 765 1346 717 0\n1352 1 58 -63 -2 0 798 1222 1247 1246 1218 1219 115 20 132 126 1315 243 731 771 779 790 793 1350 1351 692 83 1 1266 737 755 747 699 55 116 756 794 784 765 717 38 113 750 741 1320 187 763 74 71 148 112 11 252 271 352 712 1349 0\n1353 -57 58 -63 -2 0 798 113 126 1315 243 731 771 779 790 793 132 20 1350 1351 692 1266 737 755 750 741 1320 186 194 83 1 747 699 55 116 756 794 784 765 1253 788 777 767 1352 2 727 115 717 160 117 743 708 366 410 374 359 922 0\n1354 58 -63 -2 0 798 1351 132 20 126 1315 243 731 771 779 790 793 1350 194 116 115 113 1 692 83 1266 737 756 755 794 747 750 788 784 699 741 777 763 765 55 1320 767 1253 717 186 187 38 1352 2 727 1353 239 712 0\n1355 -40 -63 -2 0 1223 1240 1215 1221 1239 691 1354 103 98 148 132 117 113 541 20 11 1 49 1348 264 336 737 539 560 696 574 633 383 328 648 553 545 675 606 577 689 609 580 628 593 0\n1356 -67 40 190 39 38 36 33 0 1225 1218 798 790 793 758 137 241 1334 451 747 746 760 743 794 708 784 205 765 717 0\n1357 -63 -2 0 798 20 113 115 116 117 126 132 243 1315 731 771 779 790 793 1355 1356 696 737 756 755 794 750 784 741 743 765 1320 717 185 205 708 0\n1358 -180 -41 -2 0 205 55 48 20 1 747 750 699 743 161 708 0\n1359 -177 -171 -164 59 83 39 -2 0 1357 11 5 741 743 708 160 185 692 703 102 62 140 722 0\n1360 -28 54 -171 63 0 62 140 722 0\n1361 -46 -78 -58 -10 -53 -173 -172 -169 -41 -2 0 1248 187 186 103 98 45 510 161 329 416 386 11 64 68 198 214 266 712 727 249 895 731 0\n1362 -41 165 -2 0 1201 798 737 754 748 697 1357 20 1 48 55 205 1283 1285 735 1358 755 793 786 790 763 776 779 769 771 1359 746 699 83 161 407 692 708 98 102 739 1360 1320 186 1361 722 144 215 1257 727 201 0\n1363 -4 -110 24 -70 -131 22 21 40 -113 0 1224 1248 1243 691 661 664 672 689 628 590 245 142 545 577 580 582 589 543 625 297 688 400 673 569 665 657 662 0\n1364 -78 -70 -58 165 40 -2 0 1239 1215 1226 1223 691 1247 245 236 143 698 697 369 556 599 603 609 99 506 110 102 97 1362 541 572 588 296 442 509 568 661 664 672 689 623 612 1363 279 381 553 607 608 611 602 622 555 688 399 673 400 665 569 662 657 0\n1365 -70 -58 28 165 40 -2 0 798 1362 737 11 5 1364 703 741 750 755 793 790 1333 779 1257 771 0\n1366 -193 70 54 41 40 63 0 786 790 1333 765 776 779 722 771 65 1260 717 731 122 0\n1367 -171 -172 74 -177 70 -164 59 54 26 -2 0 1357 1251 722 1359 68 214 208 727 0\n1368 -83 -170 -172 74 26 41 40 0 203 208 1253 717 727 212 0\n1369 -172 74 72 70 -164 59 54 26 165 40 -2 0 798 737 1357 1362 1366 793 755 750 743 756 794 1367 776 784 765 1368 708 35 1253 717 191 212 727 0\n1370 -58 28 165 40 -2 0 798 1362 737 756 794 788 777 1357 98 102 103 110 694 1365 1366 793 755 750 741 1320 185 186 187 1369 767 769 779 774 784 1251 722 1359 763 765 64 198 1258 712 731 249 0\n1371 -51 -57 -18 -46 -91 -36 -83 -78 -166 -2 0 1248 25 11 266 20 1 83 374 410 366 699 921 0\n1372 54 -91 70 -36 -83 -78 -166 -164 -169 -171 58 66 -2 0 1240 1248 249 25 296 187 186 1357 20 11 1 722 495 64 266 712 1371 692 109 376 370 387 909 699 0\n1373 -59 -31 -12 -54 -91 -36 -83 -78 -166 66 -2 0 1222 1238 1244 212 187 91 464 296 20 1 109 376 370 387 907 699 0\n1374 187 28 165 40 -2 0 798 1248 1244 1238 1222 1370 1362 737 756 794 788 777 697 20 1 779 774 790 784 1251 793 763 765 1350 755 747 750 741 743 1320 185 186 187 708 203 209 1258 1253 717 25 212 1368 767 1257 731 249 1372 91 96 354 464 712 1373 692 83 374 410 366 699 919 0\n1375 -170 -83 74 -172 41 40 0 203 1368 717 25 0\n1376 -51 -65 -89 -46 -26 -3 -166 -83 -78 -2 0 1238 208 1357 503 20 1 83 374 410 366 699 1081 0\n1377 -26 -171 -3 -169 -166 -83 -78 -173 58 66 -2 0 798 1238 20 1259 793 1350 209 1257 208 296 187 1357 1 9 86 93 722 712 249 503 731 1376 692 109 376 370 387 699 1069 0\n1378 -46 26 80 74 -172 0 68 214 727 0\n1379 -59 -65 -84 -31 -54 -3 -166 -83 -78 66 -2 0 1217 1357 502 296 20 1 109 376 370 387 699 1066 0\n1380 -83 -78 28 165 40 -2 0 798 1242 1217 187 186 1374 771 769 1370 1362 737 756 794 782 697 1357 20 1 208 209 1259 1257 793 1350 755 747 1375 718 765 762 324 784 776 1377 1378 722 96 234 712 58 727 248 502 731 1379 692 83 374 410 366 699 1078 0\n1381 -193 -173 41 40 63 0 786 1333 765 1257 1366 89 1260 717 731 122 0\n1382 -53 -164 58 0 83 109 692 0\n1383 28 165 40 -2 0 798 1362 737 697 1357 20 1370 1374 771 1381 793 1350 755 747 750 743 1382 741 1326 1320 185 1380 708 0\n1384 165 40 -2 0 798 1357 737 756 794 788 1362 1383 4 29 87 170 1360 776 774 784 769 765 1253 717 191 212 727 0\n1385 175 41 190 38 -165 40 33 0 798 790 793 756 738 794 1350 784 128 765 717 0\n1386 -84 65 -173 0 219 248 731 0\n1387 -45 65 -169 -173 -28 33 0 175 10 95 712 249 1329 731 0\n1388 36 -187 41 190 -28 -165 40 33 0 1202 771 769 781 170 33 29 4 717 1356 762 696 133 1386 1387 727 201 246 731 0\n1389 -187 41 190 -28 -165 40 33 0 170 4 769 1388 59 191 212 727 0\n1390 41 171 -28 -165 40 33 0 1202 798 776 29 1389 774 788 783 794 765 760 717 747 128 696 137 1334 0\n1391 -28 40 -2 0 798 1384 1357 20 4 29 33 87 170 1360 776 1390 46 1358 1356 760 696 794 133 788 784 774 763 769 771 1387 1386 727 201 246 731 0\n1392 -80 65 -173 0 201 246 731 0\n1393 167 -179 -41 -2 0 748 205 55 48 20 1 739 741 708 746 161 699 0\n1394 -91 31 77 74 72 -169 -41 51 0 249 1277 103 712 0\n1395 -45 77 74 72 65 -169 -41 -173 51 33 0 58 1394 95 731 712 1329 0\n1396 190 -41 -187 40 -2 0 798 1358 760 794 205 48 47 46 771 769 1391 1384 1266 20 790 1356 784 793 696 763 758 755 133 736 1386 1392 1393 1320 185 186 187 1332 1382 1395 98 727 0\n1397 -169 65 -78 -171 -41 -187 51 -2 0 771 1392 1386 707 187 186 185 769 1357 20 1395 727 9 86 93 1347 1394 722 731 198 0\n1398 65 -78 -171 -41 -187 51 -2 0 798 186 185 1358 205 771 769 1357 20 1386 1392 1397 763 786 793 758 755 1332 736 1382 98 102 1378 727 722 144 0\n1399 -78 -171 -41 -187 -165 -2 0 1226 1201 798 1248 45 510 205 48 769 1266 1357 20 11 186 187 448 1398 125 133 149 696 1285 412 383 417 1316 758 754 793 736 786 692 763 98 102 722 64 266 1378 712 993 0\n1400 -67 167 83 42 39 -2 0 1225 1218 1203 20 1 137 241 699 451 745 708 739 0\n1401 74 -58 80 84 -171 -172 63 0 102 98 727 1378 144 722 0\n1402 72 -66 167 78 -171 -41 -187 51 -2 0 1201 798 1203 1244 771 133 1392 1386 1393 758 793 786 763 754 736 45 510 205 55 48 769 1357 20 1 329 291 708 739 745 1274 699 692 386 416 102 103 1401 179 237 712 64 722 500 1257 950 0\n1403 -41 -187 40 -2 0 1201 798 1225 1218 1221 1220 1239 1242 771 769 1391 1384 1266 1357 20 11 5 41 45 48 55 205 510 1396 776 1399 703 1393 758 754 793 736 786 763 1400 696 130 133 1386 1392 1402 161 228 451 473 1271 326 376 389 731 402 692 198 200 1331 102 103 1401 722 712 959 0\n1404 -70 39 -74 -187 40 -2 0 798 1244 1225 1218 1220 1221 5 1391 11 186 703 741 750 760 794 782 1357 771 1403 1381 793 755 736 758 746 748 739 237 195 179 171 1384 1266 20 1 142 147 500 1257 717 209 323 762 708 712 161 168 228 451 473 699 1334 376 389 696 692 1114 0\n1405 -171 -74 -187 40 -2 0 798 1248 1247 1218 1225 5 1391 11 186 703 741 750 760 794 782 1357 771 1403 1381 793 755 736 758 746 748 739 237 179 173 171 169 1384 1266 20 1 1251 1404 722 64 65 198 266 314 717 258 762 510 712 103 125 1382 692 731 699 1334 240 376 387 696 451 453 708 1019 0\n1406 -74 -187 40 -2 0 798 1244 1225 1218 1220 1221 1219 1240 1248 1357 771 1403 1381 793 758 748 1391 1384 1266 20 11 5 1 171 172 179 186 216 237 703 741 739 750 746 760 755 794 736 1405 726 776 784 763 765 717 35 196 203 461 708 161 168 228 451 473 699 1334 376 389 696 692 133 103 355 731 712 982 0\n1407 -72 -45 -66 -58 171 74 -179 41 -173 28 -2 0 1224 1223 1225 1218 1220 1221 798 1240 11 265 258 58 133 103 776 724 20 5 1 161 185 451 473 368 703 741 750 746 760 699 794 784 763 765 1253 196 731 249 495 712 966 0\n1408 -89 -45 65 -173 33 0 249 1329 731 0\n1409 -77 142 72 80 83 -58 -176 28 -2 0 1239 1246 1245 99 506 97 505 11 5 187 200 431 703 563 739 639 708 565 457 0\n1410 -66 83 -58 171 74 -179 41 -173 -172 28 -2 0 1202 1223 1224 691 1241 1245 1244 97 505 103 98 776 781 748 541 20 11 133 1386 1392 727 58 265 539 574 592 624 687 674 1407 1408 360 568 661 664 671 680 647 641 1409 712 762 1253 456 461 566 567 655 0\n1411 83 -58 171 -187 40 -2 0 1225 1218 798 98 776 1406 1357 771 1403 1381 793 758 769 1391 1384 20 1410 696 137 241 1334 451 747 746 760 743 794 708 784 35 765 1253 717 191 212 727 0\n1412 -58 171 -187 40 -2 0 1202 798 776 781 1406 1403 771 769 1391 1384 20 98 103 1411 203 204 208 209 1375 718 765 762 1356 784 696 794 133 760 1386 731 750 727 249 741 58 1320 712 187 0\n1413 -6 -114 24 89 40 -66 74 0 1241 691 1242 1248 1225 1217 1247 1246 1221 1220 592 510 131 130 129 128 127 549 357 597 568 613 661 625 664 688 672 673 689 668 628 626 654 593 615 566 581 598 543 551 324 301 346 475 387 0\n1414 16 83 39 58 -182 73 28 51 -2 0 1226 1221 1220 11 5 448 475 703 387 741 692 750 736 755 0\n1415 83 156 39 58 -182 73 28 89 70 46 84 51 -2 0 1245 1240 1224 1215 670 758 748 1414 154 566 708 654 655 739 668 567 1320 659 435 656 480 570 0\n1416 -45 -173 -78 73 -54 170 -3 -83 28 58 -66 -2 0 1240 1245 691 1224 798 1226 1223 91 209 133 1386 435 567 653 667 672 689 630 731 187 234 96 543 205 204 131 541 11 58 265 712 539 762 574 782 594 794 582 756 577 736 545 692 279 376 387 1014 0\n1417 -173 -78 24 -54 -83 40 58 -66 -2 0 1242 691 1245 1240 1224 1217 1238 1247 1202 187 510 234 173 146 96 91 86 541 572 128 324 543 581 589 624 687 205 203 717 209 208 1391 697 133 131 20 1386 731 435 567 653 667 680 651 1416 398 727 560 769 635 779 558 781 1385 762 736 712 1382 692 408 376 387 1169 0\n1418 -78 24 -54 -83 40 58 -66 -2 0 1242 1202 798 1216 510 234 173 146 96 86 205 128 203 717 765 783 777 324 208 697 133 131 1357 20 1 187 1417 734 771 767 470 779 781 1385 784 762 736 794 712 1382 692 760 58 335 376 387 747 727 699 1162 0\n1419 24 -54 -83 40 58 -66 -2 0 1242 798 1223 1224 234 173 96 86 1259 793 758 205 128 203 717 765 324 209 208 207 1391 133 131 20 11 5 1 510 1418 703 291 741 750 746 760 755 794 736 782 784 1382 692 762 779 699 376 387 769 771 1386 731 727 58 265 712 1015 0\n1420 -24 -3 41 39 -2 0 1226 1223 52 304 279 0\n1421 177 42 -182 58 -2 0 758 20 1 750 746 755 699 736 1382 0\n1422 53 74 159 42 54 24 185 82 -66 -2 0 798 1240 133 20 1 699 408 747 558 760 634 794 648 784 676 779 664 771 661 731 568 495 0\n1423 42 -83 40 58 -66 -2 0 1242 691 1200 798 1218 204 205 128 324 1420 1419 510 203 717 765 543 1259 793 209 1391 697 133 131 541 572 20 11 1 332 545 577 582 590 627 629 688 615 1421 741 1320 186 187 1422 109 702 1382 367 1250 736 551 631 756 1385 598 594 794 779 549 574 782 771 268 539 762 731 271 249 712 0\n1424 -83 40 -66 164 -42 58 -2 0 798 1200 1242 1218 1391 697 133 128 695 381 553 606 52 693 364 551 596 614 629 736 756 794 782 55 1357 541 20 11 203 209 324 1419 717 1385 543 762 776 779 581 771 593 1257 731 574 722 249 539 64 177 712 271 0\n1425 -182 83 28 164 -42 58 -2 0 736 693 165 54 755 1414 750 154 743 708 0\n1426 40 -66 164 -42 58 -2 0 798 55 1357 1391 1424 1425 793 790 1381 779 771 0\n1427 -28 -171 63 0 87 1360 0\n1428 -66 164 -42 58 -2 0 691 798 1216 541 572 588 695 381 553 606 52 693 364 551 596 614 622 688 673 665 736 756 794 788 1357 133 1426 38 67 197 242 731 771 779 774 790 784 793 763 755 750 741 1427 1425 1320 470 186 187 569 657 659 662 668 568 653 359 567 712 481 0\n1429 164 -42 58 -2 0 798 135 54 20 1428 696 1350 735 793 1283 1259 0\n1430 66 -83 -42 -2 0 1221 798 1216 691 1245 1217 1238 1247 1259 793 209 135 1357 541 572 588 20 696 737 1384 756 755 60 123 242 315 794 750 731 470 1339 788 741 771 569 611 774 657 622 1427 659 688 1320 664 673 186 676 665 648 662 633 568 560 492 359 395 0\n1431 18 89 57 -78 -172 -40 -59 -83 -42 -2 0 1216 1245 1244 1225 1246 1217 1238 1247 186 1357 242 470 60 38 165 387 376 1430 208 11 492 486 358 398 270 727 1026 0\n1432 -177 -40 -189 -171 28 -175 -59 -83 -42 -2 0 1216 799 777 209 1430 133 242 731 767 1357 470 720 67 60 165 387 376 208 701 741 751 1320 761 186 187 797 789 766 714 716 1431 84 722 215 478 727 1035 0\n1433 -18 74 -172 -169 -171 -164 -14 57 -40 -83 -42 -2 0 1216 1357 242 470 67 60 38 1430 131 208 165 84 232 722 712 215 727 1401 692 376 387 1036 0\n1434 74 -172 -169 -171 -164 -14 57 -40 -83 -42 -2 0 1245 67 60 38 208 1357 1433 492 722 86 234 727 712 217 0\n1435 78 57 -40 28 -83 -42 -2 0 798 209 1430 133 242 731 771 779 38 1259 793 207 165 11 5 703 291 741 750 760 755 794 736 788 784 777 774 763 767 1434 179 237 712 0\n1436 -189 -164 -78 -40 -83 -42 -2 0 1430 697 738 711 707 744 186 181 209 133 242 731 771 67 131 208 1357 777 774 767 1432 692 102 1401 722 215 0\n1437 -164 -78 57 -40 -83 -42 -2 0 1202 1217 1238 1247 1216 1204 707 187 186 1357 242 470 209 1430 133 731 67 60 38 131 208 165 1436 783 763 1347 712 398 234 239 481 722 773 767 727 98 692 376 387 1021 0\n1438 164 -42 -2 0 694 1429 0\n1439 -78 -40 -83 -42 -2 0 1216 1218 1204 1357 242 470 209 1430 133 731 67 60 131 208 1438 165 11 181 186 1437 93 96 103 147 271 359 722 692 773 376 387 1027 767 727 0\n1440 -57 -59 -40 -83 -42 -2 0 1216 1204 798 165 387 376 207 1439 291 209 1430 133 242 731 771 1357 470 67 60 208 93 96 147 235 722 773 774 767 788 794 760 750 741 1320 170 439 727 1029 0\n1441 57 -40 -83 -42 -2 0 1204 1202 1439 209 1430 133 242 731 771 60 38 208 1357 1435 4 87 170 175 1360 773 774 767 783 727 763 239 712 0\n1442 -40 -83 -42 -2 0 1430 131 1438 1441 103 1440 692 0\n1443 78 144 77 185 40 72 71 22 73 -2 0 798 1244 1222 1246 1391 11 5 291 703 563 741 638 750 644 760 561 794 426 784 1406 779 0\n1444 -57 -83 -42 -2 0 1242 1218 691 1215 1245 1220 1219 1243 1217 1244 1238 1222 1430 128 1442 324 543 581 55 203 717 765 1391 131 208 207 206 202 1438 165 1357 541 11 96 103 178 235 271 692 539 376 387 574 593 627 688 673 679 665 647 1443 442 568 661 662 668 657 653 569 567 497 502 464 1010 0\n1445 -46 89 84 -59 -78 -83 -42 -2 0 1242 1246 1217 1225 1244 1202 186 376 1430 1442 52 110 1419 486 165 387 187 1444 55 203 128 717 324 133 209 208 64 68 337 712 762 781 779 769 771 727 731 1165 0\n1446 89 84 -59 -78 -83 -42 -2 0 1242 1225 1217 1246 1244 1238 1222 691 1245 1220 1219 1243 1241 1223 1224 1430 1442 52 110 1419 376 187 186 1444 541 572 128 324 543 581 589 624 687 674 1391 208 1357 11 486 568 661 1445 464 567 653 669 668 662 673 677 657 688 648 569 627 633 497 593 560 424 574 265 539 0\n1447 -89 -59 -78 -83 -42 -2 0 1242 1202 1238 1430 1442 52 110 1419 165 387 376 186 1444 55 203 128 717 765 783 777 324 133 209 208 1357 236 249 503 731 771 767 774 722 337 1378 1161 0\n1448 -59 -78 -83 -42 -2 0 1202 55 203 1430 128 1442 717 765 783 133 52 1357 110 1419 1447 1446 214 215 1386 722 771 774 0\n1449 -84 54 -189 65 63 0 214 215 1386 722 771 774 0\n1450 152 54 74 -66 80 0 1240 1242 659 661 657 568 569 495 402 0\n1451 -78 -83 -42 -2 0 1242 691 1219 1240 1248 541 572 1430 128 1442 324 543 581 589 133 131 209 208 1438 186 187 1448 692 381 102 553 606 609 625 688 673 1450 664 668 676 653 648 567 633 478 343 560 355 0\n1452 -83 -42 -2 0 798 55 52 1357 11 5 203 208 209 1430 128 133 1442 1391 717 765 1444 1451 703 741 750 760 794 782 784 762 776 779 769 771 1406 1386 1257 731 1401 249 1419 722 64 177 712 0\n1453 -80 -192 -167 41 -66 54 -2 0 788 133 128 1357 192 1392 771 779 774 784 763 765 717 38 67 722 147 1347 0\n1454 -40 -172 -169 -171 80 84 -167 74 54 -2 0 1357 38 60 67 727 722 93 1347 0\n1455 -38 -171 54 63 0 65 142 722 0\n1456 187 -192 -167 74 41 -66 54 -2 0 1453 1357 133 788 1449 777 128 779 774 784 763 765 1455 717 197 242 1454 731 767 0\n1457 -40 -171 -173 54 63 0 67 197 722 1257 0\n1458 -36 -46 74 -172 0 25 191 1378 0\n1459 66 58 -182 -165 33 0 1266 696 1350 138 692 0\n1460 -83 58 40 -2 -66 0 1423 1452 0\n1461 80 160 70 -182 74 40 -171 -172 54 -2 0 1217 1238 1247 1244 1357 722 214 68 1384 20 727 1401 93 1459 1450 398 664 560 680 633 649 640 637 565 462 1460 0\n1462 70 -171 41 -187 54 -2 0 798 1247 691 1357 771 1457 1381 793 758 1406 1384 769 541 572 20 722 1458 314 543 581 589 624 687 1461 190 1392 133 696 1350 137 138 1367 1334 746 0\n1463 -171 41 -187 54 -2 0 1245 1221 1223 1224 691 771 769 1357 541 572 1457 1406 1462 144 145 149 215 492 1257 1392 568 469 727 569 25 261 657 323 547 662 543 576 665 582 673 590 688 627 0\n1464 -26 -152 58 40 171 -2 0 798 1223 1224 1219 691 1248 664 20 1384 776 790 793 1459 133 128 127 1460 1266 1391 726 723 541 572 259 261 352 510 547 560 576 633 580 648 589 676 624 688 687 627 677 590 668 582 654 543 566 301 1414 0\n1465 -172 74 80 -173 40 171 -2 0 798 1223 1224 1219 1391 1384 776 790 793 724 541 20 11 772 1412 1459 133 1450 1386 1464 727 1408 265 353 539 258 1413 574 0\n1466 -38 72 -168 0 35 203 708 0\n1467 189 40 -2 0 1202 798 1391 1384 20 788 783 794 765 760 747 750 1358 741 743 1320 185 1466 717 128 696 137 1334 0\n1468 40 171 -2 0 798 776 790 793 20 1384 1467 774 769 1406 1412 1459 133 771 1392 1465 0\n1469 58 -183 -2 0 1225 1218 760 750 743 756 737 1266 747 736 20 1 1382 692 699 1326 240 1452 708 451 0\n1470 -84 57 -169 31 0 217 239 712 0\n1471 -74 57 -167 -169 30 0 170 179 1291 0\n1472 28 77 -66 171 -2 0 1248 1240 1219 1204 1241 798 1202 1215 1218 1468 197 123 242 731 771 774 783 763 788 794 1469 103 38 712 1470 342 60 98 773 767 5 760 750 741 1471 727 208 726 355 743 747 20 11 1320 272 185 708 1326 386 416 979 0\n1473 77 -66 171 -2 0 1248 1240 1219 1204 1202 798 1241 1220 1221 1218 1225 1239 130 1468 60 197 123 242 731 771 774 788 794 1469 98 38 783 763 103 1470 773 767 5 760 750 741 1471 727 208 726 355 110 743 747 20 1 342 712 1472 33 708 161 451 473 699 285 984 0\n1474 -77 -167 -2 0 175 187 1320 0\n1475 171 -2 0 798 20 1468 123 197 242 731 771 774 788 794 756 760 737 747 750 741 1474 1473 696 137 1334 0\n1476 -40 -121 -83 74 66 63 0 1221 1216 691 1245 1217 1238 1247 60 242 315 470 555 569 601 657 603 659 609 664 625 688 673 676 665 648 662 633 568 560 492 359 395 0\n1477 -168 -78 66 77 -2 0 798 296 186 185 1475 1251 1357 541 572 20 1 1466 708 205 208 209 1259 1430 793 332 545 577 580 589 1476 1384 1467 696 1459 777 137 102 103 1334 1463 747 779 760 1356 794 122 212 784 1401 763 767 731 1257 249 722 712 64 0\n1478 40 177 66 -2 0 1201 798 1475 20 1384 1266 696 137 138 1334 746 758 754 793 736 790 692 779 102 1403 1463 0\n1479 177 66 -2 0 798 20 750 1478 123 197 242 731 771 779 790 793 758 755 746 737 696 137 1334 0\n1480 66 77 -2 0 1357 1475 1427 1479 741 743 1320 1477 0\n1481 -58 173 46 31 80 -167 -2 0 1202 1357 1475 1427 1320 186 102 103 722 215 1347 1401 763 767 783 777 0\n1482 -40 82 80 41 -167 77 -2 0 798 1357 1475 1427 1320 186 1480 133 38 67 242 731 771 779 1481 1469 794 1456 784 96 234 763 712 0\n1483 -167 -168 77 -2 0 1202 1480 133 128 1357 1475 1427 1251 1320 185 186 1466 708 205 208 209 1482 1467 1460 717 777 102 103 1463 1449 779 1401 781 767 762 731 1257 249 722 712 64 0\n1484 169 38 40 -192 36 -2 0 782 762 763 717 784 1403 779 0\n1485 58 40 177 -168 -66 -2 0 1201 131 1475 1251 20 1 1460 708 161 228 376 692 736 1438 754 699 746 0\n1486 -193 38 40 36 -2 0 786 790 765 779 717 1403 0\n1487 40 167 -168 -66 -2 0 798 741 750 760 794 128 1475 1357 1485 102 1455 1486 793 758 1393 717 1463 765 779 784 0\n1488 -70 -169 31 77 0 147 236 712 0\n1489 -168 77 -2 0 798 1480 133 1475 1357 1483 741 750 760 794 1487 38 67 197 242 731 771 779 784 763 1488 722 96 234 712 0\n1490 -40 77 -2 0 798 1489 743 750 760 794 1480 133 1475 1357 38 67 197 242 731 771 779 784 763 1488 722 96 234 712 0\n1491 -54 77 -2 0 1239 798 1216 1224 1248 1243 691 1490 1489 743 750 760 794 711 1480 129 506 133 131 128 127 1357 1475 1427 1251 541 572 89 91 96 102 146 234 1484 1486 712 793 260 335 1421 510 560 55 303 633 717 543 648 765 581 784 589 779 624 771 687 1386 677 1415 0\n1492 185 77 -2 0 798 1480 128 1489 743 750 760 794 1490 1357 1475 1491 1455 1484 784 766 779 721 1463 0\n1493 -173 -70 77 -2 0 1226 798 1245 1242 1357 1475 1427 1489 1480 128 1490 1491 1455 1486 793 758 748 739 1320 186 492 743 750 760 794 1484 1492 765 717 55 1421 103 1347 245 711 20 710 1332 416 386 1251 448 133 1392 1257 402 943 0\n1494 -70 77 -2 0 1226 798 1245 1242 1489 743 1480 128 1490 1357 1475 1491 1455 1486 793 1492 765 717 55 1421 103 98 711 758 20 710 1332 416 386 1251 1427 748 739 1320 448 186 750 760 794 1484 788 133 1449 777 144 1347 492 1493 733 767 341 727 947 0\n1495 77 -2 0 798 1226 1248 1357 1475 1427 1251 20 11 1480 128 131 133 1489 710 711 743 750 760 794 788 777 1490 1491 1455 1484 1486 793 758 748 739 1320 186 448 1492 765 717 55 1332 1421 386 416 98 103 1494 722 64 198 266 337 712 1394 731 985 767 1378 0\n1496 -58 54 -2 0 798 1215 1225 1218 1220 1221 1495 1474 741 750 760 794 200 177 1357 1475 722 1257 771 779 784 765 1479 128 1455 790 793 758 1393 717 748 739 746 788 777 767 441 217 179 176 1427 1251 20 11 1 272 1401 258 208 708 161 451 473 368 699 954 0\n1497 54 -2 0 798 1225 1218 1495 1474 741 1479 131 750 200 177 1475 1251 1357 722 1257 771 779 790 793 758 755 748 736 739 1496 1421 692 1452 240 708 451 0\n1498 -193 -2 0 1497 89 1495 1474 741 1479 133 128 200 790 1486 779 242 771 731 0\n1499 -2 0 798 11 1357 1475 1251 1427 1495 176 1474 741 1479 131 1497 102 270 258 510 1498 793 758 1421 748 1452 739 1414 708 154 0\n1500 -40 82 -173 0 123 242 731 0\n1501 83 170 72 92 53 51 -45 -54 -91 -171 -182 0 1222 1226 1245 1224 1243 798 1220 1221 1246 1218 1499 1239 1261 173 102 1277 313 150 58 96 85 249 1336 1251 758 471 708 454 743 750 746 760 755 794 736 737 782 692 762 107 220 376 712 1459 472 223 431 290 699 1156 0\n1502 -175 -59 -14 -42 -83 -3 -45 -54 -91 84 -190 -182 0 1499 1223 1226 799 1244 1238 1222 165 387 376 701 711 776 1336 284 706 744 751 53 51 295 102 91 737 761 1459 797 785 764 715 464 440 1171 0\n1503 -164 -14 -42 -83 -3 170 51 -45 -54 36 -91 84 -190 -182 0 1499 1223 1226 798 776 1336 284 165 58 102 96 249 692 376 387 1502 756 738 794 697 782 404 370 762 1064 712 0\n1504 -86 -77 -7 -8 -66 -14 -32 -42 -83 -3 -45 -54 -91 0 534 1038 0\n1505 -42 170 90 -45 -54 36 -91 84 -190 -182 0 1222 1218 1226 1223 1499 1225 1239 1247 798 1244 776 374 386 537 451 1501 1261 173 102 1277 313 150 58 56 96 249 1336 53 70 165 284 292 1503 695 736 1350 288 348 756 794 782 762 712 1504 484 373 1040 0\n1506 175 42 170 53 31 57 28 89 30 -182 0 798 756 755 794 747 750 782 741 762 712 187 703 14 23 699 0\n1507 90 -45 -54 36 -91 84 -190 -182 40 0 1225 1226 1222 1221 1220 1218 1499 1239 1223 798 58 173 102 96 776 243 1427 1261 249 1336 1251 374 386 537 451 1277 717 313 1501 1505 1506 736 737 692 106 107 108 220 376 382 510 1459 474 223 325 295 290 699 449 747 1152 760 712 794 762 782 0\n1508 -164 42 59 31 58 57 36 -91 -171 -182 40 0 243 1427 1261 249 1336 1251 1382 692 160 1266 737 755 1506 750 717 743 205 708 0\n1509 42 -90 -45 -54 36 -91 -171 -182 40 0 1205 798 1226 1222 1221 1220 1218 1225 1499 802 536 805 846 856 851 849 814 241 240 58 102 96 243 1427 1261 249 1336 1251 753 1508 693 736 735 378 756 1279 755 696 794 717 313 750 782 1506 743 762 161 327 289 708 712 292 1047 0\n1510 -83 -77 -7 -66 -3 -42 -90 -45 -54 -91 30 0 1226 1499 1205 1223 802 536 805 846 856 851 849 814 51 53 295 240 381 284 449 1048 0\n1511 164 170 -3 -42 -90 -45 -54 -91 -171 -182 0 1499 1223 1226 798 1221 240 381 1336 284 53 536 58 102 96 1261 249 1251 693 736 1350 378 756 755 794 750 782 743 762 712 1510 471 708 1050 0\n1512 -54 36 -91 80 84 65 -190 -172 -182 40 0 1205 1226 1223 1499 1224 1220 1219 1248 1243 798 776 1261 249 243 1336 1251 85 86 96 102 173 727 56 58 1507 240 536 802 805 846 856 851 849 814 1509 55 284 303 381 717 1511 692 160 1266 391 292 737 756 755 794 750 782 743 762 708 712 1076 0\n1513 -83 -58 -90 -66 -12 -74 -3 -42 -46 -91 30 0 1226 1499 1223 165 82 53 389 536 51 295 284 449 1144 0\n1514 -90 -168 -66 51 -12 -164 -74 -3 -42 -46 -91 -171 0 1499 1223 1226 1221 1336 284 165 82 53 1261 1251 240 536 389 692 1513 471 708 1146 0\n1515 87 -58 -83 90 -66 -12 -74 -3 -32 -42 -46 -91 0 1218 1225 53 52 82 368 165 451 292 537 411 384 1087 0\n1516 -58 -83 90 -66 -12 -74 -3 -32 -42 -46 -91 0 1218 1225 165 451 292 82 70 53 52 368 1515 531 1095 0\n1517 57 -164 -74 170 -3 -42 -46 54 -91 -171 0 1499 1223 1226 1241 798 1225 1218 1215 1336 284 706 165 135 68 1251 1471 424 762 782 794 756 760 737 750 1266 696 743 1514 451 292 708 1516 269 692 376 387 1174 0\n1518 -83 90 183 -57 -164 -74 -32 -42 -46 36 -91 0 1247 1218 1225 165 103 374 692 387 376 451 292 706 55 314 701 711 744 751 761 738 697 404 370 1062 0\n1519 90 183 -57 -164 -74 -32 -42 -46 36 38 -91 39 -182 0 1247 1225 1218 1221 103 55 314 165 53 374 451 692 292 376 387 1518 471 708 330 743 1154 750 1459 755 737 0\n1520 -164 -74 170 -42 -46 54 36 -91 65 -190 -182 0 1499 1223 1226 1247 799 1220 1219 1248 1243 55 314 776 1336 284 165 82 53 1261 243 1251 1517 103 714 764 785 797 1519 240 536 389 692 160 1266 391 292 737 1072 755 708 750 743 0\n1521 83 -74 -32 -46 38 -90 -57 -168 -7 -8 -66 -42 -91 0 1216 1221 242 55 318 536 54 471 708 1056 0\n1522 -171 -90 -57 45 164 -42 54 -91 0 798 1226 1499 1221 1216 1223 536 93 243 242 245 55 1366 793 736 755 750 743 695 694 53 1350 371 381 753 735 165 51 295 248 246 1336 1261 722 284 1385 318 779 769 727 1521 449 1054 0\n1523 -90 -57 45 164 -42 54 -91 0 798 1216 1215 1226 1223 1499 178 93 243 242 245 55 1366 793 736 755 750 743 756 794 788 695 694 53 1350 371 381 753 735 248 246 536 1522 723 776 774 338 482 1385 769 30 1466 727 284 900 0\n1524 86 -74 -14 -32 -46 -3 -83 90 -57 -7 -8 -66 -42 -91 0 1217 1225 129 485 373 1039 0\n1525 -74 -14 -91 -32 -46 -3 -83 90 -57 -7 -8 -66 -42 0 1524 534 1037 0\n1526 -57 45 164 -42 54 -91 0 798 1225 1218 1221 1216 1226 1499 1223 243 242 245 55 1366 793 736 755 750 743 695 694 53 1350 371 381 753 735 165 51 295 54 248 246 93 1523 451 1466 708 1385 318 776 779 1336 722 769 284 449 727 1525 0\n1527 45 164 -42 54 -91 0 798 1241 691 695 381 553 606 694 243 242 245 55 1366 793 53 1350 371 551 596 614 246 1526 424 560 1335 633 622 648 688 675 676 689 664 623 1450 616 361 598 549 0\n1528 164 -42 54 -91 0 798 1219 1240 1226 1223 1499 1225 1218 1220 1221 243 242 245 55 1366 793 753 53 249 694 695 736 735 1350 381 756 755 371 794 750 743 1527 58 68 95 172 353 722 495 776 784 1385 763 30 1466 712 284 451 473 887 0\n1529 -168 -32 -6 -59 -184 -45 -18 -66 57 -42 -91 0 1218 1225 1221 1216 165 240 451 292 387 376 58 128 55 54 249 242 1466 708 717 318 1163 762 712 0\n1530 -32 -6 -59 190 -45 -152 -18 -66 57 -42 -91 0 1202 1218 1225 691 798 549 597 613 617 686 240 451 165 387 376 781 128 55 247 242 292 563 638 640 645 678 671 1529 711 743 330 750 566 760 655 794 567 784 343 765 997 717 0\n1531 58 -45 -152 -18 54 -66 57 -164 -42 -91 0 1247 1202 1219 1225 1218 1226 1499 1223 1224 1221 1216 798 245 243 68 722 776 781 58 52 51 53 127 254 131 128 165 55 54 249 242 692 353 240 376 387 451 1530 284 265 30 717 318 765 762 784 712 794 1006 760 708 750 743 0\n1532 -26 30 33 22 23 24 0 1222 1499 253 0\n1533 -28 21 33 23 24 0 1499 1247 254 0\n1534 -30 1 26 21 24 31 0 1247 255 0\n1535 -31 30 33 22 21 23 24 0 1499 1246 256 0\n1536 1 -33 26 22 21 31 28 0 1246 1247 1222 257 0\n1537 5 -26 46 40 0 1224 1223 261 0\n1538 -28 45 40 5 0 1248 262 0\n1539 -32 5 40 46 45 0 1248 1224 1240 263 0\n1540 1 26 28 -40 32 0 1240 1223 264 0\n1541 1 32 28 -45 0 1224 1223 265 0\n1542 1 32 26 -46 0 1248 266 0\n1543 6 -31 54 58 0 1218 268 0\n1544 6 -32 58 54 57 0 1215 269 0\n1545 1 32 -57 28 0 1218 271 0\n1546 1 32 28 31 -58 0 1218 1215 272 0\n1547 77 13 78 74 -1 0 1241 273 0\n1548 13 77 -32 74 0 1241 275 0\n1549 1 -78 31 26 0 1241 278 0\n1550 4 -32 41 39 42 0 1226 280 0\n1551 4 -33 41 39 0 1223 1226 281 0\n1552 32 -39 33 0 1499 282 0\n1553 32 -41 30 33 0 1499 1223 283 0\n1554 32 30 -42 0 1499 1223 1226 284 0\n1555 32 30 23 -8 50 0 1499 1239 1225 1218 286 0\n1556 8 59 50 53 -32 0 1239 1225 288 0\n1557 32 -53 30 0 1499 1225 1218 289 0\n1558 32 30 -59 23 0 1239 1499 1218 290 0\n1559 32 -72 33 0 1499 294 0\n1560 -78 33 23 73 0 1499 295 0\n1561 -4 3 24 22 21 36 40 38 0 1243 1248 1224 297 0\n1562 4 -36 42 22 23 39 24 0 1224 299 0\n1563 4 -38 42 21 23 24 0 1248 300 0\n1564 -39 24 36 3 21 40 0 1248 301 0\n1565 4 42 -40 22 21 23 24 39 0 1243 302 0\n1566 3 38 21 22 36 40 -42 0 1243 1248 1224 303 0\n1567 46 -3 31 5 45 0 1247 1222 1226 1238 308 0\n1568 3 -31 41 38 36 0 1238 1226 310 0\n1569 5 -36 31 46 0 1222 1226 311 0\n1570 5 -41 31 45 46 0 1222 1247 1238 312 0\n1571 3 38 41 -45 0 1222 1226 313 0\n1572 3 -46 36 41 0 1247 314 0\n1573 -41 66 9 63 65 0 1216 316 0\n1574 -65 3 41 38 0 1221 317 0\n1575 3 38 41 -66 40 0 1216 1221 318 0\n1576 15 -41 80 82 0 1242 321 0\n1577 3 -83 40 36 0 1242 324 0\n1578 4 -11 23 41 39 50 0 1239 1220 1221 325 0\n1579 11 -41 67 53 50 0 1239 1220 326 0\n1580 4 -53 41 39 0 1220 1221 327 0\n1581 4 -67 39 23 41 0 1239 1221 328 0\n1582 5 46 -12 31 40 0 1215 1216 334 0\n1583 -31 12 65 70 0 1216 335 0\n1584 12 57 -40 70 0 1215 336 0\n1585 46 5 40 -57 0 1216 338 0\n1586 -65 5 31 46 0 1215 339 0\n1587 84 77 -40 17 0 1241 342 0\n1588 5 -77 45 40 0 1242 344 0\n1589 -82 5 45 31 0 1241 345 0\n1590 -26 12 65 70 0 1219 352 0\n1591 12 45 65 -54 0 1248 354 0\n1592 12 -58 45 70 65 0 1248 1240 1219 355 0\n1593 6 -65 54 26 58 0 1240 356 0\n1594 18 -58 89 74 0 1241 360 0\n1595 10 67 21 49 51 50 -65 0 1243 1220 393 0\n1596 9 -67 65 21 36 49 63 0 1243 1248 1219 394 0\n1597 12 -36 70 57 0 1217 396 0\n1598 12 -63 45 57 0 1247 397 0\n1599 12 45 -66 70 57 0 1247 1238 1217 398 0\n1600 9 -70 36 66 0 1247 399 0\n1601 19 80 -66 91 0 1242 402 0\n1602 20 -57 91 84 0 1242 420 0\n1603 20 -65 89 84 0 1241 421 0\n1604 -89 12 45 65 0 1242 423 0\n1605 12 45 57 -91 0 1241 424 0\n1606 14 -13 22 30 71 72 0 1246 1222 1244 425 0\n1607 77 13 71 -30 74 0 1244 428 0\n1608 -72 77 74 28 13 0 1244 1246 1222 429 0\n1609 14 72 22 -74 30 0 1222 430 0\n1610 -28 17 84 82 0 1245 432 0\n1611 13 -46 78 74 0 1245 433 0\n1612 17 46 -74 82 0 1224 1223 434 0\n1613 17 -78 46 84 82 0 1224 1240 1245 435 0\n1614 13 -82 28 78 74 0 1240 1223 436 0\n1615 13 -84 28 78 0 1224 1223 437 0\n1616 13 77 -18 78 28 0 1218 1215 438 0\n1617 18 -77 54 0 1218 441 0\n1618 18 -78 89 54 0 1215 442 0\n1619 13 -89 78 28 0 1218 443 0\n1620 16 83 -14 39 0 1223 1226 444 0\n1621 14 -16 78 30 0 1223 1226 445 0\n1622 16 -78 39 83 0 1226 448 0\n1623 14 30 -83 78 0 1223 449 0\n1624 -72 90 0 1218 1225 451 0\n1625 88 -78 85 90 0 1239 1225 452 0\n1626 14 30 -88 78 0 1225 1218 453 0\n1627 -15 16 22 39 71 72 0 1243 1224 1245 454 0\n1628 15 -16 82 80 22 38 71 0 1243 1224 1245 455 0\n1629 16 -38 72 71 0 1245 456 0\n1630 -39 15 71 82 80 0 1245 457 0\n1631 15 -72 82 80 38 0 1245 1224 1243 458 0\n1632 16 -80 22 39 72 0 1224 459 0\n1633 16 -82 71 22 39 72 0 1243 460 0\n1634 17 77 -38 84 0 1244 461 0\n1635 15 83 80 -46 0 1244 462 0\n1636 17 -80 46 77 0 1222 1226 463 0\n1637 15 -84 38 83 0 1222 1226 465 0\n1638 15 -19 38 83 82 0 1221 1216 466 0\n1639 -82 19 63 0 1221 469 0\n1640 19 -83 63 91 0 1216 470 0\n1641 15 83 38 -91 0 1221 471 0\n1642 -72 92 0 1221 1220 473 0\n1643 88 85 -83 92 0 1239 1220 474 0\n1644 16 83 -88 39 0 1220 1221 475 0\n1645 20 91 -77 70 0 1216 479 0\n1646 20 -82 89 70 0 1215 480 0\n1647 -89 17 46 82 0 1216 481 0\n1648 17 77 46 -91 0 1215 482 0\n1649 86 90 49 71 85 -18 0 1225 1217 1246 1244 483 0\n1650 86 85 49 90 -74 0 1225 1217 485 0\n1651 18 -86 54 89 74 0 1246 1217 1225 1244 486 0\n1652 90 86 71 49 85 -89 0 1246 1225 487 0\n1653 18 -90 49 54 71 74 89 0 1246 1217 1244 488 0\n1654 20 91 84 -54 0 1245 491 0\n1655 18 -70 74 0 1245 492 0\n1656 20 -74 91 70 0 1219 493 0\n1657 -84 18 54 0 1219 494 0\n1658 18 54 74 -91 0 1240 495 0\n1659 86 -80 49 85 92 0 1220 1219 496 0\n1660 19 -86 63 80 91 0 1243 1219 1220 1245 497 0\n1661 -92 49 19 91 71 63 80 0 1243 1219 1245 498 0\n1662 20 -80 70 89 0 1217 501 0\n1663 -84 19 63 0 1217 502 0\n1664 -89 19 63 80 0 1238 503 0\n1665 -22 49 0 1239 506 0\n1666 -49 22 0 1239 507 0\n1667 -146 -157 0 1199 682 0\n1668 -147 -156 0 1199 684 0\n1669 -134 -161 0 691 686 0\n1670 -135 -160 0 691 687 0\n1671 -136 -159 0 691 688 0\n1672 -137 -158 0 691 689 0\n1673 174 180 0 1201 752 0\n1674 175 179 0 1201 754 0\n1675 171 186 0 1204 773 0\n1676 184 190 0 1202 781 0\n1677 185 189 0 1202 783 0\n1678 182 193 0 798 793 0\n1679 183 192 0 798 794 0\n1680 -182 -193 0 799 795 0\n1681 -183 -192 0 799 797 0\n1682 -208 199 0 1249 847 0\n1683 -86 -83 -77 -1 -30 -58 -45 -18 -66 -42 -91 0 242 55 30 1575 53 52 82 368 534 928 0\n1684 90 -83 -77 -1 -30 -58 -45 -18 -66 -42 -91 0 1683 242 55 30 1575 53 52 82 368 127 505 129 1649 375 936 0\n1685 32 -58 190 -45 -18 -66 57 -42 -91 0 53 52 82 368 1676 58 51 127 1533 128 70 55 54 249 242 1559 1555 1541 30 717 1575 765 762 784 712 1679 760 750 743 708 1684 536 964 0\n1686 -90 -77 -3 -83 -14 -32 -58 -45 -18 -66 -42 -91 0 53 52 82 368 536 1127 0\n1687 86 -77 -3 -83 -14 -32 -58 -45 -18 -66 -42 -91 0 1686 53 52 82 368 127 505 129 1649 375 1093 0\n1688 72 -168 -32 -58 -184 -45 -18 -66 57 -42 -91 0 53 52 82 368 58 128 165 55 54 249 242 292 1466 708 717 1575 762 712 1687 534 1085 0\n1689 -77 -72 185 -32 -58 -45 -18 -66 -42 -91 0 1642 1624 53 52 82 368 55 247 246 242 715 766 719 1575 1631 1133 0\n1690 -168 -32 -58 -184 -45 -18 -175 -66 74 57 -42 -91 0 706 53 52 82 368 734 728 772 775 58 51 127 1533 128 701 55 249 247 242 744 751 761 1681 789 1688 1624 1642 1689 343 712 1608 762 962 717 0\n1691 -90 -38 -77 -16 -14 -32 -58 -45 -18 -66 -42 -91 0 53 52 82 368 536 970 0\n1692 86 -38 -77 -16 -14 -32 -58 -45 -18 -66 -42 -91 0 1691 53 52 82 368 127 505 129 1649 375 933 0\n1693 -45 54 -66 74 57 -164 -42 -91 0 246 1450 1658 697 738 128 165 82 55 53 52 249 245 243 242 58 68 722 776 1676 1531 368 1685 1690 710 711 743 292 330 750 760 1679 784 763 765 712 717 1692 534 925 0\n1694 -58 -12 45 54 -66 74 -42 -91 0 560 633 648 53 242 1335 246 1450 664 1658 52 51 127 1533 505 128 165 1560 82 55 248 245 243 98 368 727 553 769 606 609 621 1670 680 677 649 668 642 654 561 566 1611 274 1616 722 1582 774 1677 765 717 30 1629 1554 1624 1642 960 0\n1695 -32 72 58 -139 -120 -155 54 57 73 0 1544 292 549 563 597 638 613 640 621 649 1670 680 0\n1696 54 -66 74 57 -164 -42 -91 0 131 128 165 55 54 53 249 248 246 242 1658 1450 664 1693 1605 560 1335 633 1694 692 240 376 387 1624 1695 1554 30 63 1336 717 1575 776 765 1676 1677 784 762 774 1679 769 760 727 750 9 1537 743 712 708 1166 0\n1697 45 -59 -54 -66 74 57 -42 -91 0 165 51 53 1560 88 387 1626 240 1624 376 242 128 55 89 717 765 1575 52 127 129 1665 1535 1554 91 86 54 249 248 246 244 1591 727 1539 769 779 1676 784 762 1679 712 760 1170 750 708 743 0\n1698 -66 74 57 -164 -42 -91 0 242 734 243 55 1381 1678 248 128 131 1696 102 724 692 240 1697 728 1507 772 780 0\n1699 -45 -54 -182 -91 0 724 734 248 246 244 242 59 728 772 1512 780 0\n1700 -59 -36 -77 -54 66 -42 -91 0 91 88 1554 242 734 243 55 1381 1678 1699 1539 244 1591 135 696 737 755 750 743 165 51 53 1560 54 240 376 387 370 1624 1626 1063 708 0\n1701 -54 66 74 57 -42 -91 0 242 734 243 55 1381 1678 135 696 737 755 750 743 756 1679 53 1350 165 54 249 248 246 244 86 88 89 91 102 1554 19 1699 1591 727 1539 769 779 784 763 765 712 717 1700 381 692 160 374 410 292 708 917 0\n1702 59 -46 -164 -42 -18 -36 -91 0 248 171 246 25 59 727 769 779 128 135 696 737 756 1679 784 763 249 52 51 24 306 53 788 774 1336 1535 177 712 103 165 1560 1611 1554 46 31 1260 1678 755 750 743 54 381 692 160 374 410 292 708 913 0\n1703 -42 -36 54 -91 0 248 171 246 25 59 727 769 779 46 31 1260 1678 1658 128 24 249 245 243 51 52 53 54 135 165 1528 306 1560 696 737 756 755 1679 750 788 784 743 774 763 1336 722 1554 1535 177 1611 712 1702 240 376 387 370 1624 1626 708 1061 0\n1704 -59 58 42 -182 66 0 107 109 376 1459 223 737 699 755 747 0\n1705 -86 -57 -36 54 -91 0 128 46 31 1260 1678 1703 103 1704 94 753 248 171 246 25 59 727 769 1658 24 245 243 222 223 224 226 228 534 377 692 736 735 1350 756 755 696 22 23 1679 750 788 741 743 774 1251 1427 722 1562 708 1536 703 911 0\n1706 -57 -36 54 -91 0 1703 46 31 1260 1678 753 248 171 246 25 59 727 769 1658 128 24 245 243 94 103 1704 1705 412 696 737 735 756 755 1382 692 1679 747 750 72 73 76 160 374 410 406 788 699 741 743 774 22 23 1251 1427 722 1578 708 1536 703 923 0\n1707 -192 -36 54 -91 0 1706 248 171 246 25 59 727 769 779 249 245 243 788 784 774 763 722 64 177 712 0\n1708 -46 -58 -33 -168 -167 -67 -12 -18 -36 -91 0 23 22 412 534 223 241 1624 46 25 62 66 1542 703 1581 708 1003 0\n1709 -78 -4 -83 -169 46 -58 -33 -67 57 -18 -36 -91 0 412 534 245 1597 249 248 247 187 1613 712 1179 0\n1710 -28 -169 57 89 0 10 175 712 0\n1711 -83 -78 -169 46 -58 -33 -67 57 42 -18 -36 -91 0 412 223 134 510 332 1709 0\n1712 -36 54 -91 0 249 248 247 246 245 243 25 59 128 171 727 1658 769 1703 1706 1597 1707 1679 756 760 736 737 747 750 1266 696 741 743 137 241 412 1334 1624 534 22 23 138 692 1708 722 774 1677 763 1710 703 187 1613 712 1711 319 708 1181 0\n1713 189 72 36 40 0 788 1677 1679 765 760 750 743 1466 717 48 205 708 0\n1714 -31 -78 54 -91 0 242 1712 185 1713 186 248 246 245 243 9 58 64 727 722 769 774 0\n1715 190 169 72 36 40 0 763 1676 784 762 1679 760 750 743 1466 717 48 205 708 0\n1716 177 58 -171 169 31 42 57 36 -91 0 1261 763 786 1678 758 242 750 746 760 755 1679 736 782 1508 762 1274 717 0\n1717 -78 57 54 -91 0 1712 249 248 246 243 242 181 182 183 185 186 187 1557 1554 1714 712 763 786 1678 1715 776 779 1251 1261 769 1401 1716 743 708 205 717 1506 736 1508 376 1558 223 0\n1718 41 -32 -168 -171 57 54 -91 0 23 16 14 245 243 722 177 249 64 712 244 337 61 1261 1336 1251 1712 246 242 717 1572 762 1676 782 779 1679 769 756 760 1378 736 737 747 1517 1550 699 137 161 386 416 1382 696 1609 708 1143 0\n1719 -32 -168 -171 57 54 -91 0 245 243 722 177 249 64 712 763 786 1678 758 244 337 68 1251 248 247 246 14 15 16 23 510 1718 55 205 1576 1316 708 159 160 161 1624 1642 1278 1579 699 389 747 760 755 1679 737 784 696 779 1148 769 727 0\n1720 -168 -171 57 54 -91 0 245 243 722 177 249 64 712 763 786 1678 244 337 1427 1261 1336 1251 1717 1712 247 246 242 1719 1557 1554 703 741 750 1716 760 755 98 1546 1679 737 782 784 762 779 717 769 45 205 1553 1576 1378 510 708 228 1624 1642 412 419 696 989 0\n1721 -171 57 54 -91 0 1717 1712 249 246 245 244 243 242 1251 1336 1261 1427 722 61 64 177 337 712 763 786 1678 758 748 1720 710 711 743 739 1715 1635 750 703 779 760 755 12 15 16 23 769 1679 737 505 510 1378 782 1627 292 762 717 55 1316 1332 1716 696 386 416 1145 0\n1722 -74 -41 168 190 46 57 36 -91 0 710 247 246 1576 709 43 42 505 1627 790 1678 743 750 755 737 1266 736 758 746 1274 692 47 242 1715 748 739 711 249 172 179 1471 1612 1605 712 22 1356 1332 696 386 416 1139 0\n1723 -30 -77 -45 -18 -41 168 190 36 -91 0 58 790 1678 743 750 755 737 1266 736 758 746 1274 692 98 710 247 246 1576 709 43 42 505 1627 47 45 711 242 22 1534 1356 1332 696 386 416 965 0\n1724 -41 168 57 54 -91 0 1721 776 790 1678 743 750 755 737 1266 736 242 1712 710 1713 774 769 249 1715 1710 758 746 748 739 711 709 723 1717 248 247 246 42 43 47 1576 1274 505 692 1627 98 1722 1658 727 58 712 1723 703 1621 23 1356 1332 696 386 416 1132 0\n1725 -53 -58 -14 -16 -77 -45 -18 -32 -38 41 -165 39 -91 0 137 386 416 1580 696 1131 0\n1726 -42 168 57 54 -91 0 242 1712 1721 776 710 1715 790 1678 758 748 739 743 750 760 1679 784 765 1724 717 30 1471 1658 568 661 249 1710 1717 703 12 505 1629 566 654 668 15 510 292 563 638 640 645 677 1670 23 28 755 736 1698 1338 0\n1727 168 57 54 -91 0 1721 776 790 1678 758 748 1717 1712 249 248 246 242 709 710 743 739 1713 1715 750 746 774 1710 760 755 769 1679 736 737 784 765 1724 717 30 1471 703 1658 12 14 15 16 19 23 505 510 727 712 1629 292 1726 699 1382 1725 0\n1728 39 -66 41 -58 -45 -77 -32 -53 -18 -168 -91 0 161 1466 1571 167 292 416 386 708 1580 1129 0\n1729 41 -58 -45 -77 -32 -53 -18 -168 190 36 -91 0 161 167 292 1466 416 386 152 137 247 246 242 717 1571 765 784 1679 756 737 696 1728 1630 1130 0\n1730 -41 72 -168 0 48 205 708 0\n1731 -53 30 -18 74 -168 171 57 36 -91 0 776 249 248 246 242 77 78 79 80 81 161 1557 1532 1535 1713 1715 1466 712 774 769 727 1730 717 1729 765 1382 784 736 1679 756 0\n1732 -183 -32 58 53 74 -182 57 -91 0 23 14 756 760 736 737 747 1459 699 1698 0\n1733 -32 58 41 53 74 57 54 -91 0 1727 1721 776 790 1678 1712 242 14 23 1732 1679 784 765 717 1466 160 228 376 692 736 1528 755 699 747 0\n1734 180 32 58 41 -168 190 36 40 0 790 1678 760 755 1679 736 737 784 1266 765 692 717 107 1466 1559 0\n1735 -28 41 -184 57 36 -91 0 249 242 29 1710 717 762 0\n1736 58 -31 -17 -42 -3 -66 -83 -30 51 -164 57 -91 0 1698 172 1605 162 361 692 376 387 1175 0\n1737 -86 -8 -58 -31 -12 -17 -74 -42 -3 -66 -83 -30 -91 0 534 1088 0\n1738 90 -8 -58 -31 -12 -17 -74 -42 -3 -66 -83 -30 -91 0 1737 69 1650 375 1096 0\n1739 -8 -58 -91 -31 -12 -17 -74 -42 -3 -66 -83 -30 0 1738 536 1138 0\n1740 53 -3 -66 -83 -30 51 -166 -164 -169 46 57 -91 0 162 509 22 6 249 247 699 1698 172 179 1612 1605 712 1736 368 1739 0\n1741 -74 -4 -58 -53 -3 -66 -83 -30 -169 46 57 -91 0 416 386 249 247 172 179 1612 1605 712 1137 0\n1742 38 41 54 36 32 57 -91 0 1721 776 1676 1735 723 1727 1717 249 248 246 242 717 765 762 1677 784 774 1679 769 756 760 736 737 747 750 1266 741 703 22 34 157 1356 708 696 1577 1740 386 416 1382 1580 98 1741 1658 727 58 1541 1121 712 0\n1743 41 -66 -11 -72 -77 -1 -45 -18 -58 42 36 32 -91 0 1559 1642 1624 103 102 1742 331 968 0\n1744 -72 -77 -1 -45 -18 -165 -58 30 36 32 -91 0 1554 1557 247 246 168 228 1624 1642 1559 412 419 696 1743 1576 967 0\n1745 72 -170 -168 36 40 0 1466 1730 717 0\n1746 -77 -165 -72 -58 30 36 32 -91 0 103 102 1721 1717 98 248 246 175 179 1617 277 703 1744 741 727 750 769 760 774 1679 788 0\n1747 74 -140 45 77 -66 -58 -91 0 103 102 1721 723 1648 567 653 1717 98 249 248 246 1450 727 668 769 1668 774 652 1677 642 763 561 712 274 0\n1748 15 -31 -74 -12 -17 -66 -11 -33 -72 -58 42 -91 0 1642 1624 207 247 246 1576 1641 331 1142 0\n1749 45 -165 -72 -58 30 36 32 -91 0 103 102 1721 723 1746 1648 228 412 696 1557 1554 168 1642 419 558 1559 1624 776 1717 249 242 1605 560 635 1747 170 703 741 750 760 1679 784 763 765 712 1748 27 1141 717 0\n1750 -165 -72 -58 30 36 32 -91 0 1557 1554 168 1642 419 228 412 1559 1624 103 102 1721 776 1676 723 1717 249 247 246 696 1746 1648 1749 58 172 712 1658 763 784 1679 760 750 741 703 29 1735 1119 1631 0\n1751 175 190 78 57 30 32 89 0 790 1678 756 755 1679 750 784 741 763 703 1710 0\n1752 -58 30 36 32 -91 0 249 102 103 1717 1721 1727 776 1751 737 1750 1466 1730 1742 0\n1753 -59 30 32 0 376 1558 223 0\n1754 78 57 -167 175 30 32 -91 0 249 243 1751 703 776 87 1360 0\n1755 57 41 -165 175 -7 -86 30 32 -91 0 242 734 243 1381 1678 755 750 743 741 756 1679 1557 224 225 223 1555 363 534 228 249 248 247 246 244 1754 186 187 1717 86 90 91 1699 708 1551 1613 1591 727 769 779 784 763 765 712 1745 1070 128 696 0\n1756 -165 -86 58 30 32 -91 0 1753 226 692 736 756 1679 377 228 734 246 245 243 242 1279 1381 1678 755 750 741 743 1755 93 96 1712 1745 765 784 776 779 1427 722 769 703 1378 186 0\n1757 -86 58 30 32 -91 0 1753 734 243 242 226 228 692 1756 735 1673 753 750 1678 743 1381 1730 0\n1758 174 -91 0 734 243 242 1673 753 750 1678 743 1256 1381 1730 0\n1759 -190 -167 -182 36 30 32 -91 0 248 246 245 244 243 242 776 779 1427 769 703 1512 186 1717 722 93 1378 0\n1760 51 58 30 32 -91 0 1757 412 1753 1758 734 243 242 692 736 756 1679 735 1279 696 1381 128 1678 755 750 741 743 1759 784 765 1745 717 185 29 703 0\n1761 -28 30 32 -168 -91 0 243 242 87 1360 1712 776 1752 1760 160 1266 1745 737 765 756 784 1679 0\n1762 36 190 72 30 32 -168 -91 0 242 1752 1745 1760 765 1266 784 737 1679 756 0\n1763 190 -78 30 32 -168 -91 0 187 185 180 1554 249 248 247 244 1762 59 1712 1591 90 91 96 102 708 1613 1760 73 74 166 374 410 1266 406 1560 1562 737 1082 756 712 1679 763 784 0\n1764 30 32 -177 -182 -91 0 743 741 242 1761 703 185 186 1730 1763 776 779 1759 1251 769 718 708 1375 0\n1765 32 -177 -182 -91 0 743 248 246 242 1764 6 7 22 30 34 63 88 157 162 1336 708 1712 1730 776 1577 1745 1713 1356 1742 765 774 93 95 103 178 1545 1585 784 769 1734 1648 1679 727 747 756 736 737 1382 1266 696 699 692 376 387 1020 0\n1766 -74 46 -66 -3 -83 51 -166 -164 -169 -14 -32 -167 -91 0 15 510 23 18 14 247 242 172 1612 1471 1539 103 1382 692 699 376 387 1176 0\n1767 171 -66 -83 51 -166 -164 -169 -189 -14 36 -32 -177 -91 0 242 1577 23 18 16 14 743 741 248 246 723 724 774 769 1766 1658 727 95 1698 1731 699 0\n1768 57 74 -171 -66 -183 -32 -91 0 760 747 756 736 23 14 1721 1698 102 699 1382 0\n1769 -83 72 36 190 -32 -177 -91 0 242 743 1745 765 784 1679 756 737 1266 760 747 736 1715 1713 1466 15 510 292 23 14 734 245 243 204 1577 1356 696 1767 780 772 729 1768 96 103 178 359 722 1382 692 1548 699 376 387 1167 0\n1770 72 36 190 -32 -177 -91 0 23 18 743 741 242 1745 1715 765 784 1679 756 760 736 747 1769 708 90 1251 1326 1382 103 1471 1731 1658 0\n1771 -42 -164 57 74 -72 171 36 -32 -91 0 160 228 376 692 724 1658 15 510 161 23 1624 389 412 1642 776 19 16 249 248 246 242 55 1698 405 404 696 737 756 1679 788 784 774 763 765 769 712 717 727 1041 0\n1772 -38 -45 -77 -66 42 -58 -18 -72 -32 -91 0 161 1642 15 510 419 23 1624 389 14 12 1563 1135 0\n1773 -164 57 74 -72 171 36 -32 -91 0 724 1658 15 510 161 23 1624 389 228 412 376 1642 160 776 790 1678 19 16 14 249 248 247 246 242 692 1771 699 419 747 760 755 1679 737 788 784 696 774 763 765 769 712 727 1772 1631 717 1134 0\n1774 57 74 -72 171 36 -32 -91 0 161 160 724 1773 694 1733 1278 0\n1775 74 -72 171 36 -32 -91 0 228 376 160 16 248 246 1774 95 103 727 692 769 736 774 756 788 1679 0\n1776 164 53 -182 54 -32 -91 0 23 14 736 1528 755 699 747 0\n1777 171 36 -32 -177 -91 0 15 510 23 18 741 247 245 244 242 723 724 776 790 1676 1770 1678 159 160 161 228 1624 1642 1775 376 412 389 172 1612 553 1539 567 606 547 653 609 576 667 580 585 621 1670 680 651 1776 692 103 1592 1471 560 763 762 635 784 558 1679 1579 379 756 717 737 978 696 0\n1778 -58 -171 -91 0 102 103 1721 0\n1779 -72 -164 58 0 160 228 692 376 0\n1780 -164 -177 54 -171 -32 -91 0 743 245 243 722 1721 1712 1778 1251 15 510 23 16 14 734 246 244 242 1382 1779 292 1730 1745 1770 708 1381 1572 779 1678 769 1378 1520 332 699 747 755 737 1266 1459 692 408 376 387 1151 0\n1781 -177 54 -171 -32 -91 0 245 243 722 1721 1712 1778 1261 1251 15 510 23 16 1758 734 246 242 743 1780 693 695 736 1528 735 1279 1381 1572 1385 1550 1678 779 1350 1776 769 371 161 386 416 1378 292 708 1053 0\n1782 164 -171 -91 0 1778 1261 1336 1758 734 248 246 244 243 242 693 736 735 1760 1279 23 1381 1385 1678 779 1350 755 769 128 750 1512 1781 0\n1783 175 83 180 33 -171 -91 0 1778 1782 1779 1382 734 243 242 1674 755 1332 1678 1381 0\n1784 -41 54 51 -171 -91 0 1778 1782 692 138 1336 1760 23 1781 750 706 744 711 1783 737 696 1251 376 534 1644 1261 1641 245 243 722 1721 1779 15 510 292 108 1382 1277 1579 1149 0\n1785 54 51 -171 -91 0 1778 1336 1760 23 16 14 1782 1382 1261 734 246 245 244 243 242 1712 722 1781 750 760 1679 1784 1381 717 1678 765 758 784 746 779 699 769 1520 1378 0\n1786 51 -171 -91 0 1778 1782 1779 1382 1261 1336 248 246 242 1760 692 12 13 15 16 230 505 1666 510 806 811 1682 850 1785 96 173 1269 1277 1678 1699 1732 727 1679 769 779 784 765 717 128 1701 1704 0\n1787 -180 -32 -171 -91 0 23 1786 131 73 1778 1782 1382 747 750 699 1781 96 173 1701 0\n1788 -32 -171 -91 0 1786 1266 737 23 1787 755 1783 1678 1259 0\n1789 -193 -171 -91 0 1788 1786 1266 737 1674 748 71 72 74 229 806 166 75 151 811 1682 850 1778 1782 1779 243 1427 1336 1251 246 245 790 1259 1269 779 708 1721 722 769 739 93 1378 703 186 0\n1790 -171 -91 0 1786 1266 737 1788 1789 1678 1765 755 750 0\n1791 58 32 -91 0 1790 776 790 1678 1765 750 760 1679 784 765 755 737 1266 736 758 746 724 1712 242 1760 692 30 1274 717 0\n1792 32 -91 0 1790 776 790 1678 724 1712 1765 1791 103 1752 1727 705 744 0\n1793 -91 0 242 246 248 1790 723 724 776 1712 790 1678 758 1792 14 15 16 23 706 1777 510 744 750 746 709 710 711 1727 760 755 1713 292 95 103 178 1585 1679 736 737 774 1620 1382 1648 784 1266 1459 769 699 1332 765 692 727 717 376 387 1153 0\n1794 -38 63 -189 -57 0 1793 125 96 196 1455 731 774 771 0\n1795 -190 63 -57 0 1793 147 125 96 776 779 722 771 198 731 0\n1796 177 -182 36 -57 -32 0 758 147 103 96 706 23 750 744 760 755 710 711 1679 736 737 788 1382 1459 1332 132 1794 1795 784 765 717 67 197 722 1500 774 771 0\n1797 -170 40 38 -168 -182 36 58 -32 0 23 14 717 1745 55 161 1779 699 736 747 755 0\n1798 -164 -166 83 -168 58 33 0 1382 1779 708 1326 0\n1799 -187 171 -182 36 -57 -32 0 1793 776 725 1796 743 125 103 23 771 775 731 1794 197 209 1797 765 784 1679 760 747 1798 756 736 0\n1800 -74 -19 -59 -14 -40 -42 -83 -66 46 -57 -32 0 1793 15 510 387 376 209 147 1656 1612 1031 0\n1801 171 -182 36 -57 -32 0 1793 1796 743 235 178 103 96 95 15 510 23 16 14 723 725 1675 1799 774 788 1677 1679 765 756 760 736 737 747 1382 1779 1266 1459 1798 699 1745 292 692 208 209 1640 376 387 1500 767 1800 1651 727 1548 1030 0\n1802 63 -42 -164 173 -182 36 -57 -32 0 1793 1796 743 1801 1251 103 1779 708 208 1730 15 510 292 1466 771 779 235 147 96 23 16 722 1640 67 477 1572 1713 1797 777 765 767 784 1378 1679 756 737 1266 1459 692 376 387 1159 0\n1803 -59 -40 127 66 -42 98 33 0 104 105 550 552 1344 595 604 610 0\n1804 74 -8 -51 -40 -172 -63 -42 -14 -83 -57 -32 0 410 374 208 235 178 96 95 13 1666 12 505 16 1653 727 1548 916 0\n1805 -166 -164 82 -182 36 -57 -32 0 1793 15 510 103 1779 292 1796 743 1801 1251 708 1382 125 731 771 779 92 548 147 23 14 1334 699 70 1802 111 118 132 554 696 600 737 756 1679 788 784 777 765 767 1745 1803 692 1556 374 410 1804 1656 1612 915 0\n1806 -164 82 -182 36 -57 -32 0 1793 125 731 771 779 1801 1796 743 147 103 96 23 1779 1805 747 760 755 1679 737 784 1459 765 132 1745 722 67 0\n1807 82 -182 36 -57 -32 0 1793 1801 1796 743 147 125 103 96 23 731 771 779 1806 736 1350 756 132 1679 1455 722 784 67 765 1797 0\n1808 -182 36 -57 -32 0 147 96 1801 1807 198 1315 722 0\n1809 -190 -57 0 1793 125 779 1795 771 1315 731 0\n1810 -57 -32 0 1793 12 505 23 18 13 103 178 1809 790 1678 1808 128 171 212 400 1350 359 1548 1602 569 1779 568 561 1606 570 563 658 638 663 644 666 647 1667 0\n1811 58 172 66 65 -182 33 0 1793 1350 1459 1382 1779 737 756 755 1679 747 750 788 1326 743 777 708 767 209 731 0\n1812 -183 66 33 0 756 760 737 747 696 137 1334 0\n1813 -36 190 -32 0 1793 790 1678 23 19 16 59 115 122 128 171 191 212 727 769 1811 102 1812 1679 788 784 777 774 763 767 731 198 200 722 1488 0\n1814 -82 54 -169 -189 -32 0 18 1810 706 1471 19 1470 23 16 198 200 201 1315 712 1488 1329 722 727 774 769 0\n1815 172 54 66 190 -32 0 1793 23 1812 1679 788 784 763 1814 765 777 1813 790 1678 14 769 767 774 731 1500 1251 126 1258 1455 717 1356 55 696 737 755 747 750 699 743 161 708 0\n1816 175 187 63 -58 66 190 -32 0 102 1815 772 732 18 1810 706 23 1812 1679 784 763 1471 19 1470 788 774 1401 403 208 1455 1251 765 790 1678 1350 1813 15 14 738 755 698 747 750 369 743 708 161 1624 1642 368 699 55 717 67 722 1488 1655 1042 0\n1817 187 63 -58 66 190 -32 0 102 1815 18 1810 706 23 1812 1679 784 763 1471 19 1470 788 790 1678 758 774 1251 1401 208 1816 737 696 137 241 1334 1624 746 708 743 0\n1818 -173 54 66 190 -32 0 1793 1815 23 1812 1679 788 784 763 1814 18 1810 706 1471 19 1470 765 1813 790 1678 758 16 14 731 1500 124 1258 727 192 717 48 55 1316 696 737 755 747 750 699 743 161 708 0\n1819 -58 66 190 -32 0 18 1810 706 23 1812 1679 784 763 1471 19 1470 765 788 1813 790 1678 16 14 102 1815 1818 771 774 1817 1251 116 194 727 60 1253 1356 55 205 696 737 755 747 750 699 743 161 708 0\n1820 66 190 -32 0 790 1678 1810 706 23 19 18 16 14 1350 1812 1679 784 763 765 1470 1471 1819 1459 1382 1779 737 755 747 750 1326 699 743 55 708 1466 1253 208 1258 727 1811 0\n1821 72 39 74 84 -170 -186 -168 36 26 0 1745 708 60 197 1500 208 767 727 0\n1822 -38 -189 -66 0 1793 133 132 89 196 1455 731 774 771 0\n1823 54 -80 -72 -42 -8 -171 -40 -169 -7 58 -66 -32 0 1642 1624 67 18 1810 706 1471 132 19 1544 722 1488 1655 885 0\n1824 53 175 58 190 -32 0 1793 756 1679 788 1813 790 1678 755 750 743 784 765 1820 1822 1797 197 1500 771 774 777 767 18 1810 706 763 1471 19 1470 697 738 695 371 747 133 130 23 16 14 1556 1326 699 55 1821 1624 1642 1253 727 1823 234 1591 1654 712 886 0\n1825 175 58 190 -32 0 1820 1813 790 1678 1810 706 19 18 16 756 755 1679 750 788 784 743 777 763 765 1470 1471 1822 1797 197 1500 771 774 1824 1251 161 1821 0\n1826 -54 -42 -169 84 -83 -40 -14 -59 -66 -32 0 1793 132 1640 60 15 510 387 376 133 1810 19 234 1591 1654 712 1024 0\n1827 84 74 -168 -171 -170 58 190 -32 0 1793 1820 132 1825 736 1779 1251 708 1640 1813 1745 67 15 510 131 692 387 376 292 1382 1810 23 19 16 14 1821 777 788 1677 1679 763 760 747 699 1826 1544 722 1488 1655 1033 0\n1828 -84 -83 -40 -171 58 190 -32 0 1793 1820 132 1640 67 15 510 131 1825 736 692 387 376 1779 292 1382 133 1810 183 23 19 17 14 215 422 1470 1615 722 763 1025 784 699 1679 747 760 0\n1829 -168 -171 -170 58 190 -32 0 1793 1251 15 510 1820 131 1825 736 692 387 376 1779 292 1382 132 1813 1810 706 23 18 14 1745 708 67 197 1640 1828 1827 173 1612 1471 361 722 763 1034 784 699 1679 747 760 0\n1830 54 -80 -169 -42 -40 -16 -171 -14 -59 58 -66 -32 0 18 1810 706 1471 67 15 510 387 376 132 19 1544 722 1488 1655 1000 0\n1831 -171 38 -170 58 190 -32 0 1793 15 510 1820 131 1825 736 692 387 376 1779 292 1382 133 1813 790 1678 758 1810 706 23 19 18 16 14 1251 1829 711 743 1332 1620 750 746 1253 717 760 699 197 1500 1679 788 784 777 763 767 1470 1471 727 1830 234 1591 1654 712 1157 0\n1832 168 171 38 -170 72 53 36 -179 33 0 711 743 1332 750 717 760 197 1500 1679 771 788 774 0\n1833 38 -170 58 190 -32 0 1825 736 1779 1382 1813 790 1678 758 1810 706 23 19 18 16 1831 1675 1832 1745 197 1500 771 774 788 1677 1679 763 760 1470 1471 747 1821 1326 0\n1834 -38 72 -66 36 0 40 1822 1713 0\n1835 58 190 -32 0 1793 1820 133 132 131 1813 1676 1810 15 510 706 23 19 18 16 14 1825 736 1382 1779 692 292 376 387 1834 1833 720 721 765 762 1713 1575 784 1470 1471 777 1679 760 747 750 1326 699 743 708 208 209 1640 731 771 767 774 1378 727 144 722 234 1654 712 1160 0\n1836 -77 170 190 -32 0 1793 14 765 784 1679 760 747 23 750 743 1677 1820 133 1676 762 1835 102 1814 731 771 774 1251 18 1810 706 1471 777 767 19 1470 132 1401 208 708 161 699 15 368 1642 1624 193 721 719 720 1575 177 1617 1588 722 1115 0\n1837 170 190 -32 0 1793 1835 102 1820 133 132 1676 1810 706 23 19 18 15 14 719 720 721 765 762 1575 1677 784 1470 1471 777 1814 1679 731 760 771 767 747 750 774 743 1251 1401 193 208 708 161 1624 1642 368 699 1836 712 1488 1548 1604 722 1147 0\n1838 77 -41 -171 -72 190 -32 0 1793 1835 18 1810 706 14 161 23 55 699 747 760 1679 784 763 1471 1820 132 102 133 788 1449 777 1814 731 767 1401 193 130 139 1579 15 368 1642 1624 19 712 1488 1548 1604 722 990 0\n1839 -171 40 -72 190 -32 0 1793 23 15 1835 161 368 1642 1624 1837 102 1820 139 133 132 130 1813 1810 706 18 14 1455 717 55 1579 699 747 760 1679 788 784 777 1449 763 1471 1814 731 767 1401 193 1838 177 1617 1588 722 958 0\n1840 -77 40 -72 190 -32 0 1793 1839 1675 726 23 15 1835 161 368 1642 1624 1837 102 1820 133 1813 16 14 179 200 217 1617 1645 731 771 767 774 788 1679 760 747 699 55 717 192 467 727 941 0\n1841 -38 -45 77 -72 190 -32 0 1793 1820 193 1601 172 1548 213 23 15 1835 161 368 1642 1624 1810 19 14 1822 1634 788 1677 1679 763 760 712 747 961 699 0\n1842 -45 40 -72 190 -32 0 1840 23 15 1835 161 368 553 606 609 617 1669 1837 102 1820 139 130 1813 14 172 193 1548 1450 561 664 683 1841 717 55 1579 699 558 747 634 760 650 1679 644 788 784 637 763 565 1814 1576 0\n1843 40 -72 190 -32 0 1793 161 1837 1820 697 133 1813 1810 706 23 19 18 16 14 1839 723 726 1675 1842 1539 1599 560 1330 731 771 767 774 788 1677 1679 763 760 1470 1471 747 727 699 192 55 717 0\n1844 77 -12 -80 -169 -42 -72 190 -32 0 18 1810 706 1471 19 1470 1843 23 15 1835 161 368 1642 1624 1820 1587 712 1548 983 0\n1845 -80 189 -42 -72 190 -32 0 1793 1677 763 1843 23 15 1835 161 368 1642 1624 102 1820 1810 730 770 778 726 1584 1844 1617 1645 946 0\n1846 189 -42 -72 190 -32 0 1793 1843 197 1500 67 60 23 15 1835 161 368 1642 1624 207 102 1820 132 1810 706 19 18 16 1677 763 1470 1471 1845 1601 320 727 767 1675 722 1488 1655 942 0\n1847 80 -42 -72 190 -32 0 1793 1843 197 1837 1820 697 1835 694 738 706 710 744 701 751 761 1681 1846 789 766 715 67 132 102 1500 771 774 722 478 777 767 133 1449 60 23 15 161 368 1642 1624 207 16 1601 320 727 953 0\n1848 -42 -72 190 -32 0 1843 197 1500 771 67 706 710 744 23 15 1835 161 368 1642 1624 1837 1820 697 694 738 102 132 701 751 761 1681 1846 789 774 766 722 715 478 1847 195 1655 1548 952 0\n1849 -72 190 -32 0 1835 102 1820 133 132 1810 706 23 19 18 15 14 158 161 1624 1642 368 1843 49 67 197 1500 771 1848 1550 408 699 747 760 1679 788 784 777 1449 774 763 767 722 1471 1488 1401 1655 1117 0\n1850 -70 -80 42 -40 190 -32 0 208 195 49 15 510 1849 292 1835 1820 790 1678 758 23 19 14 13 143 1655 1550 1632 708 743 750 746 760 699 1679 386 416 784 1108 763 1488 0\n1851 77 -39 -53 -169 -12 -80 -40 190 -32 0 416 386 218 195 15 510 1849 292 1835 1820 1810 19 1587 712 1548 981 0\n1852 -80 42 -40 190 -32 0 1793 197 1500 771 67 15 510 1849 292 1835 102 1820 132 1810 23 14 208 1850 722 1584 774 788 1677 1679 763 760 747 750 699 743 386 416 708 1851 1617 1645 945 0\n1853 171 80 -40 -32 0 197 1500 771 60 1810 706 19 18 16 1675 774 767 1677 763 1470 1471 727 0\n1854 -169 42 -40 190 -32 0 1793 15 510 1849 292 563 638 640 645 49 1852 1853 1251 1550 545 577 580 585 620 1669 678 67 1820 132 1835 102 722 215 1601 569 657 197 1500 1810 706 23 19 18 14 1471 1488 1401 1655 767 568 777 662 788 669 1679 654 760 566 747 1620 699 386 416 1101 0\n1855 42 -40 190 -32 0 1793 197 1500 67 60 49 15 510 1849 292 563 638 640 645 1835 102 1820 132 23 16 14 1852 1601 569 657 659 1853 1251 722 1550 215 545 577 580 585 620 1669 678 671 1854 715 763 1587 1677 784 567 777 1679 655 767 760 566 727 747 1620 699 386 416 1105 0\n1856 -90 169 80 -40 190 -32 0 1793 1855 54 15 510 1849 292 563 638 640 645 1835 110 381 553 606 609 617 1669 678 1820 1601 569 657 659 671 67 132 102 1853 722 215 715 1587 567 655 566 1620 16 60 197 1500 763 1677 777 767 727 536 948 0\n1857 86 169 80 -40 190 -32 0 1793 1856 1855 54 15 510 1849 292 563 638 640 645 1835 110 381 553 606 609 617 1669 678 1820 1601 569 657 659 671 67 132 102 1853 722 215 715 1587 567 655 566 1620 16 60 197 1500 763 1677 777 767 727 13 1666 1650 375 940 0\n1858 169 80 -40 190 -32 0 1793 15 510 1849 292 563 638 640 645 1835 110 1855 381 553 606 609 617 1669 678 1820 1601 569 657 659 671 67 132 102 1853 722 215 54 197 1500 60 16 715 763 1587 1677 567 777 655 767 566 727 1620 1857 534 932 0\n1859 -86 80 -40 190 -32 0 1793 1855 54 15 510 1849 292 563 638 640 645 1835 110 381 553 606 609 617 1669 678 1820 1601 569 657 67 132 102 1853 722 18 1810 706 1858 1471 1655 568 662 669 654 566 1620 19 1488 534 931 0\n1860 90 80 -40 190 -32 0 1793 1859 1855 54 15 510 1849 292 563 638 640 645 1835 110 381 553 606 609 617 1669 678 1820 1601 569 657 67 132 102 1853 722 18 1810 706 1858 1471 1655 568 662 669 654 566 1620 19 1488 13 1666 12 505 375 1649 939 0\n1861 80 -40 190 -32 0 1793 15 510 1849 292 563 638 640 645 1835 110 1855 381 553 606 609 617 1669 678 54 67 102 1820 132 1810 706 19 18 1601 1853 569 722 657 1858 1471 1488 1655 568 662 669 654 566 1620 1860 536 944 0\n1862 -90 -40 190 -32 0 19 67 1820 132 1835 102 23 790 1678 758 1813 1855 82 1849 1837 1834 54 1861 208 708 1832 722 743 750 760 1679 784 763 1488 195 1655 13 1632 110 381 15 510 292 536 951 0\n1863 86 -40 190 -32 0 1862 537 19 67 1820 132 1835 102 23 790 1678 758 1813 1855 82 1849 1837 1834 54 1861 208 708 1832 722 743 750 760 1679 784 763 1488 195 1655 13 1632 110 381 15 510 292 1666 1659 375 934 0\n1864 -40 190 -32 0 1813 1820 1849 1834 15 510 292 1837 1835 110 102 132 790 1678 758 23 19 13 67 1855 54 82 381 1861 195 208 1632 708 743 1832 750 722 760 1655 1679 784 763 1488 1863 534 926 0\n1865 -70 190 -32 0 1793 1835 18 1810 706 1849 1813 1864 1715 1471 1820 133 1713 102 1814 731 777 767 19 1470 132 771 774 1401 23 790 1678 758 1834 1837 717 1745 711 1332 416 386 15 510 329 292 340 1655 1488 949 0\n1866 190 -32 0 1793 1810 15 510 706 183 23 19 18 790 1678 758 1813 1820 132 133 1835 102 1837 1849 292 1834 1864 1745 1715 1713 717 711 1470 1471 1814 777 329 1332 731 767 386 416 771 774 1401 193 1865 722 1599 177 1611 987 712 0\n1867 -53 -89 -14 -58 -80 40 -32 0 208 1866 776 1251 153 708 743 750 1620 195 183 194 779 771 201 1257 102 722 1611 1392 133 137 386 416 407 696 1055 737 1381 755 1678 0\n1868 -89 -14 -58 -80 40 -32 0 1810 12 102 23 18 13 1866 779 771 1392 133 776 1251 208 1620 566 654 667 195 183 194 201 1257 722 1611 561 563 638 644 647 680 1670 1338 153 708 743 15 510 14 1867 368 699 746 758 1674 1678 737 1366 696 412 417 991 0\n1869 -14 -58 -80 40 -32 0 195 183 1866 776 194 779 771 201 1257 102 722 1611 561 1392 218 208 1251 563 1620 638 566 644 654 647 1667 669 1868 1603 1594 570 568 656 662 0\n1870 89 153 -58 -65 84 74 0 1603 1594 570 568 656 662 0\n1871 -146 -58 -80 40 -32 0 195 218 1866 779 771 1392 183 776 194 201 1257 102 722 1611 561 642 645 23 15 12 505 18 13 1869 1606 161 368 553 133 101 1642 413 556 599 607 611 619 1670 677 665 1870 188 564 562 636 643 1624 121 559 679 646 1671 632 622 557 585 1057 581 322 543 0\n1872 -58 -80 40 -32 0 1866 779 771 1392 133 201 1257 218 195 194 776 15 510 12 505 183 23 18 13 100 101 102 722 1611 561 642 645 1869 1606 1626 161 1624 1642 417 368 413 553 556 599 607 611 619 1670 677 665 1870 1871 649 634 558 1579 379 322 1052 0\n1873 14 -13 58 66 -174 -32 0 15 510 12 505 183 18 13 1606 1626 1779 417 735 696 0\n1874 -89 58 66 83 -32 0 1866 776 1251 1283 1810 15 510 183 23 18 17 16 13 12 234 362 1619 549 561 597 613 617 1669 1873 563 1620 638 566 644 654 647 667 680 683 1670 650 619 1338 634 615 614 558 598 606 382 406 418 551 553 367 378 377 388 1196 0\n1875 -13 -80 40 -32 0 208 1866 779 771 1392 133 1872 1874 23 1812 1679 782 776 1251 1283 192 191 1810 19 174 1873 712 153 763 762 786 717 1678 758 1350 1332 1382 0\n1876 -14 -80 40 -32 0 193 195 1875 1548 1588 547 576 580 585 620 1669 218 1866 779 771 1392 208 133 1872 1874 1603 570 656 659 192 191 776 1251 23 15 13 12 563 1620 638 566 640 654 645 668 677 681 1670 649 624 621 634 586 609 613 558 582 603 606 596 543 599 553 551 1574 1566 556 366 383 367 1285 1195 0\n1877 -80 40 -32 0 1866 779 771 776 1251 15 510 183 18 208 1392 1283 133 1872 1876 1626 292 417 1779 696 735 0\n1878 -41 14 58 40 -32 0 1793 1866 779 771 15 510 183 18 1626 417 776 1251 1623 1283 292 1779 735 696 133 731 200 775 1822 128 710 1624 161 1810 23 19 41 721 1331 1797 712 1678 763 786 0\n1879 14 58 40 -32 0 1793 1866 779 775 771 776 1251 1810 15 510 183 19 18 1626 292 1623 417 1779 1283 736 735 756 696 1679 128 133 1822 782 731 200 1878 717 762 1814 712 234 0\n1880 170 38 41 -165 58 40 -32 0 1793 1879 563 638 153 1877 1866 779 771 776 1251 1810 12 505 706 183 23 18 17 13 765 786 1678 1459 133 1601 1575 731 569 543 209 1633 657 581 708 566 659 585 743 654 620 750 668 1669 760 681 1679 647 782 644 762 561 1471 1614 0\n1881 38 41 -165 58 40 -32 0 1877 1866 779 769 16 1880 717 1253 171 212 727 0\n1882 -38 -171 0 89 116 1455 0\n1883 74 63 54 80 -32 0 1866 779 769 776 16 1378 722 144 215 727 0\n1884 -74 -41 -165 72 58 -32 0 1793 1730 205 1810 706 23 18 1281 1471 736 763 1382 786 1332 1678 758 0\n1885 -63 -173 0 1793 126 1315 731 0\n1886 -65 74 -165 58 80 -32 0 1866 779 769 1810 23 19 16 124 133 727 1459 1470 1678 763 786 0\n1887 -165 58 40 -32 0 1793 1879 563 638 153 1877 1866 779 771 1885 776 1882 15 510 183 17 1881 329 566 654 1884 1883 1886 1386 731 1654 1639 1614 570 569 561 658 644 660 647 669 1667 0\n1888 -82 74 165 72 58 80 -32 0 1866 779 771 1885 1883 234 23 697 1812 1679 782 737 1674 776 1882 769 1251 1810 19 16 200 209 219 712 1283 727 762 735 1253 1382 1332 0\n1889 74 58 40 -32 0 1793 23 1887 697 1812 1679 782 737 1879 153 1877 1866 779 771 769 1810 19 16 1888 731 122 124 727 1470 763 762 786 1745 1678 743 755 750 0\n1890 58 40 -32 0 1793 1866 776 1882 1251 1810 706 23 18 1879 153 1887 697 1812 1679 782 1889 171 1471 762 1745 717 711 1286 0\n1891 165 40 -32 0 18 1810 706 1877 1866 779 771 1885 1890 102 1883 1471 763 786 1678 171 776 1882 23 14 697 737 1812 755 1679 747 750 782 743 762 1745 717 161 55 699 0\n1892 -41 -72 40 -32 0 1793 1866 776 779 771 1885 1890 102 1891 228 412 696 133 731 198 722 19 1877 1883 172 1589 13 1666 12 505 1642 1661 23 15 161 368 1624 100 1579 1116 0\n1893 -72 40 -32 0 1793 1891 1877 1866 779 771 1885 1890 102 1883 172 171 776 13 1666 12 505 23 19 15 161 228 1624 1642 368 412 1661 553 696 569 606 133 657 609 731 659 198 1589 664 722 547 672 1672 628 587 1892 323 543 1113 583 331 578 545 0\n1894 -183 72 -32 0 1793 1866 779 771 776 1251 23 760 1812 750 133 743 731 708 209 0\n1895 40 -32 0 1793 1866 779 771 1885 776 1882 1810 15 510 13 1666 12 505 706 23 19 18 1877 1890 102 1883 171 172 1471 763 786 1678 758 1891 1893 292 1894 1679 782 762 1745 717 711 329 1332 1316 386 416 696 1661 133 731 198 1589 722 1107 0\n1896 -32 0 1866 779 771 1895 197 1500 0\n1897 168 -66 -40 0 1793 1896 132 131 123 197 731 771 779 790 1678 758 748 67 38 743 739 750 760 755 1679 736 788 784 774 763 1336 1427 1753 703 692 187 102 1488 722 0\n1898 -58 -192 80 63 -40 0 1793 123 197 731 788 777 767 771 779 784 763 774 67 60 38 98 102 722 1449 1488 727 179 0\n1899 -192 39 -66 72 -40 0 1793 1896 1897 708 208 132 131 123 197 731 771 779 790 1678 720 67 39 38 788 784 777 774 763 1336 1427 1753 1898 692 736 755 750 741 703 186 187 1488 722 86 96 1821 1470 0\n1900 -84 -13 -42 -59 -83 -66 -40 0 1793 1896 123 197 731 771 1753 1336 774 1677 763 88 7 220 240 450 376 132 1640 38 211 1470 1657 1540 1028 0\n1901 74 77 -42 -59 -83 -66 -40 0 1896 1793 123 197 731 771 1753 1336 774 1677 763 1675 767 141 220 240 450 376 132 1640 208 127 505 60 38 1607 1900 727 1587 93 1590 1023 712 0\n1902 77 -42 -59 -83 -66 -40 0 1896 1793 123 197 731 771 1753 1336 774 1677 763 141 220 240 450 376 132 1640 67 38 1901 237 276 1612 1656 712 1032 0\n1903 58 -166 -164 -83 33 -66 -40 0 1896 1793 132 1640 208 131 123 197 731 60 692 1382 220 240 376 1753 450 223 88 141 1336 699 1675 767 1902 178 179 217 1645 1617 1584 727 1022 0\n1904 -77 26 -167 39 -168 72 -40 0 1896 720 39 175 179 187 217 703 1821 1336 1675 0\n1905 171 74 57 26 39 -168 72 -40 0 1793 123 197 731 771 720 39 38 1675 774 1821 1677 1470 763 0\n1906 74 33 -66 72 -40 0 1896 1897 1552 1899 1679 760 750 741 708 756 736 747 1903 98 1904 103 102 132 720 67 39 38 1905 722 215 1488 1821 763 777 1677 0\n1907 33 -66 72 -40 0 1793 1896 1897 123 197 731 771 38 1552 708 1899 1679 756 760 736 747 750 741 1903 98 103 1904 1906 170 186 237 703 712 1336 763 774 1677 0\n1908 -74 -66 72 -40 0 1896 1793 139 1907 380 558 634 22 129 1665 197 67 38 195 276 1612 1609 1601 539 567 563 569 573 653 638 657 588 640 659 620 649 668 1669 681 0\n1909 39 1 -66 72 -40 0 1896 38 270 1908 1907 107 1897 132 131 1899 1679 756 736 692 98 103 1546 1905 1360 0\n1910 1 -66 72 -40 0 1793 1896 1907 107 131 123 197 731 771 38 1909 33 1251 1546 774 692 788 736 1679 756 0\n1911 171 80 26 74 59 51 -40 0 1793 123 197 731 771 60 38 1675 774 767 788 1677 727 1679 763 756 1470 736 103 692 0\n1912 -171 -66 72 -40 0 1910 2 1908 1907 107 1897 132 131 720 67 39 38 1251 1899 1679 756 760 736 750 692 741 102 1904 722 215 1488 1821 763 777 1677 0\n1913 90 86 -89 -78 -12 -58 -39 -80 -1 -33 -66 -40 0 535 197 218 67 1613 139 380 127 505 129 1652 385 938 0\n1914 -90 -89 -78 -12 -58 -39 -80 -1 -33 -66 -40 0 197 218 67 1613 139 380 536 980 0\n1915 -66 72 -40 0 1793 1896 123 197 731 771 67 60 38 131 139 1897 1907 22 107 380 1908 1910 2 3 1912 726 774 1911 788 1677 208 218 1679 763 708 756 760 736 750 692 741 103 1592 703 187 1613 712 1914 1913 534 930 0\n1916 -39 -80 66 -40 0 1793 1896 123 403 218 190 197 731 771 67 60 38 33 34 143 164 1251 1552 1540 1753 774 788 1677 1679 763 756 760 736 737 750 1266 696 741 692 412 417 703 103 1592 187 1613 712 1017 0\n1917 -80 72 -40 0 1793 1896 1915 123 197 731 771 779 790 1678 758 748 67 38 194 208 1916 708 743 739 750 760 755 1679 736 737 788 784 1266 696 774 763 138 1336 1427 692 703 102 187 722 1488 0\n1918 -169 -58 -171 39 74 72 -40 0 1793 1896 103 102 98 1336 1917 1915 123 197 731 67 60 49 38 1470 727 767 777 788 1679 756 760 1812 737 750 163 1551 696 741 743 417 412 1904 708 1587 712 1488 1604 722 113 1540 703 1011 0\n1919 -58 -171 39 74 72 -40 0 1793 1896 1336 1917 1915 123 197 731 771 779 60 49 98 102 103 1918 716 763 1594 1677 784 777 1679 767 756 760 1812 727 737 750 163 1551 1449 422 696 741 743 417 113 412 708 1540 703 1004 0\n1920 -175 58 59 0 736 737 692 1266 0\n1921 26 -63 54 -78 28 -4 -7 -33 -67 -172 -83 -169 74 80 -40 0 1896 250 221 1643 412 60 38 727 1540 1657 1470 908 0\n1922 54 -78 28 -4 -7 -33 -67 -172 -83 -169 -171 74 80 -40 0 38 187 1488 250 221 1643 412 123 67 722 1921 93 211 1590 712 1587 1065 0\n1923 -54 -192 74 80 -40 0 1793 123 197 731 788 777 767 771 779 784 763 60 38 86 96 727 1470 0\n1924 28 -4 -7 -33 -67 54 -172 -83 -169 -167 -171 74 80 -40 0 1896 1336 703 1922 0\n1925 -28 54 -171 0 113 1360 0\n1926 -67 -83 58 -171 39 74 80 -40 0 1793 1896 1336 1753 1920 756 1679 1923 1925 123 197 731 788 777 767 771 779 784 763 790 1678 755 750 741 747 1557 49 1334 372 1551 1924 0\n1927 26 -4 -11 -51 -63 -78 28 54 -172 -83 -169 74 80 -40 0 1896 166 73 1560 410 374 60 38 727 1540 1657 1470 920 0\n1928 -171 39 74 72 -40 0 1793 1896 1917 1915 123 197 731 771 779 790 1678 753 67 38 1336 1554 1753 1919 1920 756 755 1679 750 788 784 741 743 777 763 708 767 202 206 504 1923 1925 703 187 1488 722 1926 696 735 692 73 74 166 374 410 406 1560 1565 1927 93 211 1590 712 1587 1077 0\n1929 171 74 72 -40 0 1793 1917 1915 123 197 731 771 774 788 1679 756 1812 737 107 1266 1911 1920 98 0\n1930 74 72 -40 0 1929 1251 1928 0\n1931 30 -74 -40 0 1793 1896 237 186 179 170 123 197 731 771 779 790 1678 38 1753 703 741 750 760 755 1679 1920 784 103 763 712 0\n1932 72 -40 0 1793 123 197 731 771 1915 1930 1931 22 1336 1812 774 1679 788 0\n1933 171 -40 0 1793 1896 1932 158 49 1559 1551 161 157 1554 168 1642 419 228 412 1931 1753 1624 185 160 123 197 731 771 60 38 726 774 788 1677 1679 763 756 760 737 1920 750 696 98 103 1592 741 1911 1470 703 1610 1140 1710 0\n1934 -183 -40 0 1896 1933 1932 157 1753 185 756 760 1920 750 102 741 1925 703 0\n1935 -58 -40 0 1793 1896 123 197 731 1934 1679 788 777 767 771 779 784 763 1933 1932 158 49 1559 1551 161 157 1554 168 1642 419 228 412 1931 1624 185 790 1678 67 60 38 98 102 103 1925 1470 1546 703 727 741 194 750 722 755 1488 1655 737 956 696 0\n1936 -40 0 1793 1896 123 197 731 771 779 790 1678 753 1932 157 160 185 228 1753 412 1933 1935 1920 692 755 735 750 696 741 132 703 1427 0\n1937 -28 -171 0 87 113 1360 0\n1938 -66 82 -168 72 -192 0 1936 1793 128 133 1745 731 765 771 784 779 0\n1939 -170 -83 41 74 -186 0 1936 1793 209 1375 1258 767 731 0\n1940 -165 -4 -33 -89 -26 -46 -65 -3 66 -19 -83 -78 58 0 163 1266 696 365 412 417 1067 0\n1941 -33 -46 66 -19 -83 41 -78 58 -171 0 1936 1793 1896 187 1336 1753 1920 756 1679 782 788 777 186 1939 762 765 784 1809 64 712 779 769 208 1378 209 771 731 718 1577 1259 1678 753 1251 1551 1940 698 735 380 692 374 410 1079 0\n1942 -168 -78 63 54 58 -171 0 1896 1793 186 185 1336 1753 1920 756 1679 788 777 1554 1557 1251 1730 708 209 1259 1640 1678 755 747 1938 1939 765 784 779 771 1257 722 1941 1350 699 692 73 0\n1943 -19 -11 -51 -89 -46 -65 82 -33 -41 -172 -16 83 -78 38 0 410 374 186 189 1638 1378 1071 0\n1944 -51 -89 -46 -65 82 -41 -172 83 -78 54 58 -171 0 1896 64 1336 1553 1251 1622 1554 1882 374 410 406 1943 401 190 1593 1549 914 0\n1945 -80 -67 -7 -89 -46 -65 -33 -41 -16 -78 54 58 0 333 417 412 64 190 1593 1549 904 0\n1946 82 -78 63 54 58 -171 0 1896 1936 1793 1251 1942 711 1622 1336 1753 1920 743 750 755 1678 790 779 771 1381 333 1553 769 1809 786 763 1283 187 186 184 180 1882 731 1257 133 722 64 712 1944 692 365 735 696 412 417 1945 1628 401 1378 903 0\n1947 -78 63 54 58 -171 0 1896 1336 1753 1920 186 187 1942 743 750 755 1678 786 790 763 779 769 1946 198 201 219 722 144 1488 727 9 0\n1948 63 54 58 -171 0 1896 1936 1793 1336 1753 1920 756 1679 788 1674 748 1937 1554 1557 1251 1947 703 741 739 750 1673 755 1678 786 790 1259 763 779 708 769 771 160 168 228 1624 1642 1559 1779 1381 365 412 419 735 696 133 1449 731 1392 198 200 1639 722 144 1488 9 1543 727 884 0\n1949 -63 175 -171 0 1936 1896 756 1679 1937 1882 1336 1251 115 1885 771 779 790 784 1678 765 755 717 750 205 741 743 708 703 185 0\n1950 51 -4 -33 -65 -84 -3 -31 66 -19 -83 -174 -78 -54 58 59 0 163 692 365 735 696 412 417 1068 0\n1951 -33 -182 -78 58 -171 0 1936 1793 1896 185 1251 1336 1753 1920 755 750 743 708 209 756 1679 788 777 1949 1948 173 1730 1939 765 784 779 771 731 1554 1557 1937 96 234 1506 58 86 208 769 727 718 1577 1938 1640 753 1551 1950 374 410 406 1080 0\n1952 -182 -78 58 -171 0 1896 185 1336 1753 1920 756 1679 1554 1557 1251 755 747 750 743 708 209 1938 1951 1350 699 692 73 0\n1953 -84 -65 -11 -51 -33 -41 -31 -16 83 -78 -54 63 38 0 410 374 1663 1637 1074 0\n1954 82 -11 -51 -33 -41 -173 -172 -31 -16 83 -78 -54 63 38 0 1793 410 374 58 173 91 86 731 1953 1654 1613 727 1073 0\n1955 -82 45 -172 -54 0 173 86 201 219 727 0\n1956 -51 -78 58 -171 0 1936 1896 1336 1753 1920 1949 1948 1952 1678 790 779 769 187 234 96 786 763 712 58 1955 771 1381 1553 1251 1259 1622 1554 1882 406 1954 0\n1957 84 -67 -7 -65 -33 -41 -172 -31 -16 -78 -54 0 1793 333 417 412 58 1955 173 91 86 1654 1613 727 901 0\n1958 -78 58 -171 0 1936 1896 1793 1336 1753 1920 1949 1948 234 96 1882 1251 187 1952 1678 786 790 1259 763 779 1283 1622 712 769 771 58 1381 1553 333 1955 731 133 1956 692 365 735 696 412 417 1957 1663 1637 902 0\n1959 58 -171 0 1896 1793 1937 1336 1753 1251 1920 1674 748 1949 1948 96 234 1958 703 1751 741 739 779 750 769 771 1673 755 1678 786 1259 763 708 228 1779 412 735 696 133 731 200 1955 712 58 0\n1960 -90 -16 -14 -11 -66 -33 -41 -74 -31 -70 -82 -58 0 1315 1639 536 1109 0\n1961 86 -16 -14 -11 -66 -33 -41 -74 -31 -70 -82 -58 0 1960 1315 1639 99 1650 375 1092 0\n1962 -66 -193 -74 -31 -82 -171 0 1936 1896 1336 733 1315 1381 1553 700 45 1680 1959 102 198 722 1639 99 1665 97 505 694 1554 1557 1251 697 408 738 759 749 740 710 1609 1633 1961 534 1084 0\n1963 72 -193 -74 -31 -82 167 -171 0 1896 1936 1959 102 1315 198 722 171 1962 1600 733 1381 45 510 1336 1553 1639 99 1665 97 505 1251 1609 1730 1633 739 748 1674 737 696 412 417 1158 0\n1964 -193 -74 -31 -82 167 -171 0 1936 1896 171 1959 102 1315 198 722 1639 733 101 1336 1554 1557 1381 45 1553 510 1962 1600 1963 1624 1642 419 413 1043 0\n1965 -172 -31 -82 83 167 -171 0 1896 713 1959 102 1315 198 722 144 1639 733 219 201 741 750 98 1336 1554 1557 1882 1251 772 727 780 171 1964 1678 791 758 755 766 748 737 721 739 1568 708 168 228 1624 1642 1559 331 412 419 696 1112 0\n1966 -31 -82 83 78 -171 0 1896 1936 1959 102 1315 198 722 236 1639 1937 1336 703 741 750 760 1679 103 1554 1557 1882 1251 1965 729 769 1655 1614 779 790 784 1751 1678 765 737 758 748 739 708 168 228 1624 1642 1559 412 419 696 128 1100 717 0\n1967 -82 83 78 -171 0 1936 1896 1937 1336 703 741 750 760 1679 782 1959 102 98 1554 1557 1882 1251 198 200 201 219 1315 1639 722 144 1966 1488 340 1546 763 762 786 784 1678 779 758 755 769 748 737 727 739 171 708 717 168 228 1624 1642 1559 412 419 957 696 0\n1968 -74 -169 31 57 0 179 237 712 0\n1969 77 -80 -41 -169 -66 -72 31 78 -171 0 1896 193 1959 103 1968 133 132 1336 1557 1554 168 1642 419 1559 1624 1937 1546 102 712 1488 1547 1604 722 988 0\n1970 -182 -172 31 83 78 -171 0 1896 1793 1936 1959 1937 1546 1967 1336 703 741 750 760 1679 788 103 102 1554 1557 1882 1251 758 755 748 737 739 708 168 228 1624 1642 1559 412 419 696 128 132 133 1449 731 771 779 784 763 765 717 1968 1401 193 1969 177 1588 1617 722 955 0\n1971 -72 -89 -13 -46 -80 -41 -65 -1 -171 0 1896 45 510 1336 1553 133 1959 101 1554 1557 1624 1642 419 413 898 0\n1972 -172 31 83 78 -171 0 1793 1936 1896 1959 1937 1546 1967 1336 703 103 102 1970 1678 786 790 763 779 1470 1968 771 1885 1257 731 1381 1401 722 133 45 1553 177 1611 510 712 1971 1730 329 293 739 748 1674 737 696 412 417 996 0\n1973 172 82 83 167 39 0 1793 741 750 760 1679 788 777 769 767 779 731 790 133 1678 758 755 748 737 739 696 708 250 1642 0\n1974 175 83 78 -171 0 1896 1251 1937 1336 703 1967 1973 1972 233 64 1959 103 102 1949 1751 722 779 1257 771 0\n1975 -173 46 82 -171 0 1959 102 1885 1257 722 0\n1976 74 -17 84 -70 -41 -66 -11 -72 -31 -172 78 -58 0 1896 1559 1642 1624 233 58 97 505 102 99 98 274 727 1653 1111 0\n1977 83 78 -171 0 1896 1936 1793 1937 1336 703 741 750 760 1679 788 1959 97 505 102 99 1554 1557 1882 1251 1967 1973 1972 64 176 1974 737 1975 732 771 779 790 784 1678 765 758 748 739 708 168 228 1624 1642 1559 412 419 696 128 132 717 722 1449 478 1976 195 1631 1661 1110 0\n1978 -70 78 -171 0 1896 1936 1977 209 208 205 1937 1336 703 741 750 760 1679 788 777 1959 98 1882 144 215 1257 771 767 779 727 784 171 765 717 0\n1979 63 78 -171 0 1896 1936 1793 1978 1251 1977 205 1336 1557 1937 703 741 1259 1678 758 746 750 760 1679 207 209 711 1938 755 737 696 1334 1551 545 577 134 1623 563 638 640 645 788 777 1959 99 1665 102 98 97 1882 1640 569 657 659 664 676 1671 627 722 1542 539 573 590 582 543 1574 1561 731 171 1458 767 0\n1980 78 -171 0 1896 1936 1937 1882 1336 703 741 750 760 1679 1977 205 1979 115 1885 717 771 765 779 784 0\n1981 -1 -4 -67 -33 -63 -3 -83 -169 -172 82 -171 0 163 417 412 1980 186 1959 98 208 1378 187 103 8 1470 712 727 1613 1172 0\n1982 -63 -3 -183 -169 -172 82 41 -171 0 1896 1980 185 1251 760 750 743 708 208 756 737 186 1959 99 1665 103 102 98 97 1937 132 1812 696 163 1551 412 417 1981 1541 1536 1598 727 1184 1657 0\n1983 173 36 41 -171 0 1936 1980 185 1713 777 1882 717 765 186 1959 102 1251 732 733 771 767 779 784 1715 1679 760 750 743 708 208 1577 1982 1449 1401 0\n1984 -4 -89 -1 -3 -33 -19 -58 -65 -67 -78 -83 -46 -88 0 1168 412 0\n1985 -83 36 41 -171 0 1793 1896 1936 1983 1885 1882 717 765 1980 187 186 185 1959 103 98 1251 208 209 1577 1640 731 1975 133 64 1542 1378 769 779 784 1715 1679 712 756 1812 737 163 1551 696 417 1984 0\n1986 -65 -3 36 41 -171 0 1936 1896 1882 717 765 1980 185 1251 1985 708 743 750 760 1679 784 779 769 782 762 786 1678 755 737 758 746 1622 1983 1885 187 186 1959 103 102 98 1336 1557 133 149 696 722 221 241 412 1334 64 1542 1378 1625 1551 712 1177 0\n1987 65 -172 -173 -171 0 1885 1980 186 1959 1386 1392 1401 0\n1988 36 41 -171 0 1936 1980 185 1882 1251 717 765 1983 1985 708 743 750 760 1679 784 779 769 1987 1574 1986 0\n1989 -173 41 -171 0 1896 1793 1959 1980 186 1988 115 191 212 1401 769 779 790 1678 758 400 718 128 122 187 185 99 1665 97 505 102 1336 1557 1251 768 731 1939 198 1633 708 722 743 1655 750 746 760 755 1679 737 784 696 763 221 241 412 1334 1488 1625 1551 1194 0\n1990 46 41 -171 0 1793 1980 185 1251 1959 186 1988 115 191 212 1401 1989 767 777 788 1679 760 750 743 708 128 756 737 696 412 1812 163 417 1551 1677 763 733 400 187 102 722 1613 1655 1488 1193 0\n1991 41 -171 0 1793 1896 1980 187 186 185 1959 103 98 1251 1988 115 122 128 191 212 400 1401 1989 767 777 788 1677 1679 763 756 760 1812 737 750 163 1551 696 743 417 412 708 1990 64 1542 337 712 1007 0\n1992 -19 -89 -46 -67 -171 0 1936 1896 1793 1959 98 1542 198 1991 45 510 417 412 1980 185 46 1713 777 1251 205 1622 1336 1553 186 1882 189 1638 1378 1009 767 731 0\n1993 -169 -46 -67 63 -171 0 1896 1793 1959 98 1542 64 1980 707 742 1336 1991 1553 700 749 694 698 738 759 1680 45 510 417 412 139 1251 205 1622 721 187 103 766 712 791 780 1992 1660 730 772 732 1573 337 1016 0\n1994 -46 -67 63 -171 0 1896 1936 1793 1991 45 510 417 412 1980 1251 205 1622 1336 1553 46 186 185 1959 102 98 198 1542 1993 716 1715 1618 477 779 769 771 1378 731 1001 0\n1995 -187 65 -171 0 769 771 1987 0\n1996 -82 -67 63 -171 0 1896 1936 1959 102 1994 722 236 1980 187 103 1991 46 185 149 1995 779 1715 712 139 1600 186 1655 45 510 417 412 1251 205 1622 1336 1553 1639 1191 0\n1997 -67 63 -171 0 1896 1936 1980 185 1991 46 1713 777 1251 205 1622 45 510 1336 1553 187 186 1959 103 102 139 412 417 1994 722 149 215 236 1655 1600 1995 779 1715 712 1996 1257 1613 767 1192 1401 0\n1998 -88 -17 -31 -70 -80 -66 -11 -171 0 1896 1980 186 1655 1251 1991 205 1622 1336 1553 1959 535 1090 0\n1999 90 -17 -31 -70 -80 -66 -11 -171 0 1896 1998 534 1980 186 1655 1251 1991 205 1622 1336 1553 1959 97 505 99 375 1649 1098 0\n2000 -70 -80 82 -66 -169 -11 -171 0 1896 1980 1251 1991 205 1622 1336 1553 187 186 1959 1655 1488 478 1999 536 1106 0\n2001 -90 -89 -12 -46 -80 -66 -11 -171 0 1896 1959 98 1542 1980 1251 1991 205 1622 1336 1553 536 986 0\n2002 86 -89 -12 -46 -80 -66 -11 -171 0 1896 2001 1959 98 1542 1980 1251 1991 205 1622 1336 1553 97 505 99 1652 375 937 0\n2003 173 65 63 -171 0 1936 1896 1997 1980 185 1991 1730 743 750 1995 779 790 1678 755 737 696 46 1715 1959 102 1713 1449 1336 1553 380 777 1251 205 1622 187 186 103 98 733 767 1401 193 2000 722 1592 64 1542 712 2002 534 929 0\n2004 -86 -31 -70 -19 -82 -66 -11 -171 0 1896 1980 186 1655 1251 1991 205 1622 1336 1553 1959 534 1089 0\n2005 90 -31 -70 -19 -82 -66 -11 -171 0 1896 2004 1980 186 1655 1251 1991 205 1622 1336 1553 1959 97 505 99 375 1649 1097 0\n2006 65 63 -171 0 1896 1936 1793 1336 1991 1553 1997 380 1980 185 1730 743 750 1251 205 1622 46 187 186 1959 102 1995 779 790 1715 1678 755 737 696 2003 731 198 1639 722 1655 1488 2005 536 1102 0\n2007 -90 63 -171 0 1896 1959 1980 186 102 2006 149 722 214 185 1991 1730 743 750 1997 133 696 737 755 1678 790 779 769 1401 64 187 103 786 763 712 98 1542 101 100 99 97 1595 1336 1553 380 1251 205 1622 536 896 0\n2008 86 63 -171 0 1896 2007 1959 1980 186 102 2006 149 722 214 185 1991 1730 743 750 1997 133 696 737 755 1678 790 779 769 1401 64 187 103 786 763 712 98 1542 101 100 99 97 1595 1336 1553 380 1251 205 1622 505 1652 375 881 0\n2009 63 -171 0 1896 1980 185 1991 1730 743 750 1251 205 1622 1336 1553 187 186 1959 103 102 101 100 99 98 97 1997 380 2006 133 149 1595 696 722 737 64 214 1542 755 1678 786 790 763 779 712 769 1401 2008 534 879 0\n2010 -89 -171 0 1896 1936 1991 45 510 2009 132 1949 737 696 417 412 1980 185 46 1713 777 1885 767 1315 205 468 194 118 1251 1622 1336 1553 186 1959 98 233 239 1647 1549 727 1013 0\n2011 -171 0 1896 1936 1251 1336 1959 98 102 103 1980 185 186 187 1991 45 46 205 1553 510 1713 1622 777 2009 126 132 148 194 1315 1885 1949 468 1995 767 737 779 696 1715 412 417 2010 1618 712 58 1583 727 1183 0\n2012 -46 0 2011 723 0\n2013 -54 0 2011 724 0\n2014 -63 0 2011 725 0\n2015 -70 0 2011 726 0\n2016 186 0 2011 1675 0\n2017 -190 0 2011 776 0\n2018 -193 0 2017 790 0\n2019 184 0 2017 1676 0\n2020 182 0 2018 1678 0\n2021 174 0 2020 753 0\n2022 179 0 2020 758 0\n2023 176 0 2022 748 0\n2024 89 80 -78 -58 -41 0 2017 1936 2011 2020 2013 2014 185 1730 743 750 755 737 46 1713 774 771 769 1715 205 48 1622 45 510 44 1560 187 186 103 98 47 1618 712 58 727 1386 1663 1637 133 696 412 417 1188 0\n2025 -67 -86 80 -78 -58 -41 0 1793 1936 2011 2014 534 46 185 1713 774 771 186 98 769 2024 239 727 124 731 233 1549 1664 205 48 1622 45 510 44 1560 43 1666 42 1596 1005 0\n2026 -86 80 -78 -58 -41 0 2020 2014 1793 1936 2011 46 185 1713 774 771 186 98 769 2024 239 727 124 731 233 1549 1664 1730 743 750 755 737 205 48 1622 45 510 44 1560 534 2025 380 696 927 0\n2027 90 80 -78 -58 -41 0 2014 1793 1936 2011 2020 185 1730 743 750 755 737 2026 412 696 45 510 44 1560 380 46 1713 774 771 186 98 769 2024 239 727 124 731 233 1549 1664 205 48 1622 43 1666 42 505 1652 375 935 0\n2028 80 -78 -58 -41 0 1936 2011 2020 2014 1793 185 1730 743 750 755 737 46 1713 774 771 769 205 48 1622 45 510 44 1560 186 98 2024 233 239 1664 1549 727 124 731 2026 412 380 696 2027 536 969 0\n2029 -89 -78 -58 -41 0 1936 2011 2020 2012 45 510 185 1730 743 750 755 737 46 1713 774 771 2028 1392 133 696 417 412 187 1636 193 205 48 1622 44 1560 98 233 1549 1570 1018 0\n2030 -78 -58 -41 0 1936 2017 2011 2020 2012 2013 2015 103 45 510 205 48 46 44 185 187 1560 1622 1730 1713 1715 743 774 750 771 755 737 2028 1392 1636 133 696 412 417 2029 1618 1662 712 1189 0\n2031 -80 -16 -33 -58 -41 0 2011 2023 1896 2017 2020 2012 1936 154 1730 743 750 755 737 46 1715 103 2030 22 739 703 1710 175 1713 774 771 1621 45 510 193 1392 1636 1538 133 696 412 417 995 0\n2032 -67 -86 -16 -33 -58 -41 0 2023 1896 2017 1793 1936 2011 2014 534 46 154 1713 774 771 103 1715 2030 22 1730 739 703 10 1470 1471 98 769 2031 727 124 731 1710 1664 1621 43 1666 42 1596 1155 0\n2033 -86 -16 -33 -58 -41 0 2020 2014 2023 1896 2017 1793 1936 2011 46 154 1713 774 771 103 1715 2030 22 1730 739 703 10 1470 1471 98 769 2031 727 124 731 1710 1664 743 750 755 737 1621 534 2032 380 696 1083 0\n2034 90 -16 -33 -58 -41 0 2014 2023 1896 2017 1793 1936 2011 2020 154 1730 743 750 755 737 2033 412 696 380 46 1713 774 771 103 1715 2030 22 739 703 10 1470 1471 98 769 2031 727 124 731 1710 1664 1621 43 1666 42 505 1652 375 1091 0\n2035 -16 -33 -58 -41 0 1936 2017 2023 2011 1896 2020 2014 1793 22 2030 103 98 46 154 1621 1730 1713 1715 743 739 774 750 703 1471 769 771 755 10 1710 737 1470 2031 1664 727 124 731 2033 412 380 696 2034 536 1128 0\n2036 -82 -28 -45 -89 -33 -58 -41 0 2014 700 45 510 2035 329 710 704 744 751 193 1664 728 124 721 716 766 81 55 1642 419 1624 694 101 733 772 775 789 1681 761 738 697 1573 413 1045 0\n2037 -28 -45 -89 -33 -58 -41 0 2014 1793 2012 2011 193 1664 124 81 55 45 510 2035 329 1642 419 48 205 1644 417 1624 2036 731 1576 1647 771 1120 774 696 788 737 1679 756 0\n2038 -45 -89 -33 -58 -41 0 2014 1896 2020 2011 1793 233 81 55 45 510 2035 329 1642 419 48 205 1644 417 1624 22 2030 124 193 1664 2037 703 1619 1546 741 750 760 755 1679 737 788 696 774 975 771 731 0\n2039 180 45 84 74 67 26 0 2020 2011 760 755 1679 737 788 696 774 133 769 771 1392 727 0\n2040 -82 -66 -89 -33 -58 -41 0 2012 1896 2015 2014 2038 103 1599 2030 22 98 45 510 48 205 2035 1644 417 237 239 2039 750 741 703 233 1570 81 55 329 1642 419 1624 1639 1118 0\n2041 -66 -89 -33 -58 -41 0 1896 2015 1793 2012 2016 2030 22 98 45 510 48 205 2035 1644 417 237 239 2038 2039 750 741 703 233 1570 81 55 329 1642 419 1624 103 133 1599 2040 731 1647 767 1136 727 0\n2042 -89 -33 -58 -41 0 1896 2011 2012 81 55 45 510 2035 329 1642 419 48 205 1644 417 1624 22 2030 101 98 233 237 238 239 2038 1570 2039 750 741 703 2041 696 413 737 756 1679 788 774 769 771 727 1392 1636 1058 0\n2043 -28 -173 -33 -58 -41 0 2014 1793 1896 2017 2015 2011 2042 45 510 48 205 2035 1644 417 22 2030 103 1751 737 696 133 731 1646 1639 1392 1386 81 55 329 1642 419 1624 98 170 1710 439 763 1099 1677 727 774 769 0\n2044 -173 -33 -58 -41 0 1793 2014 1896 2017 2015 45 510 48 205 2035 1644 417 22 2030 103 2042 1751 737 696 133 81 55 329 1642 419 1624 98 1386 731 200 1639 1646 2043 703 741 750 760 1679 784 763 712 58 1583 2039 1104 0\n2045 -33 -58 -41 0 2011 1896 2030 103 22 2042 2044 771 774 788 1677 1679 763 760 1710 750 703 741 0\n2046 89 -58 -41 0 2022 2013 2020 2017 1793 1896 1936 2011 2014 2015 46 2045 1559 1713 774 771 48 47 1356 1730 743 750 755 737 696 133 731 1639 200 1449 205 1332 416 386 1715 1553 446 103 98 1646 712 58 1583 2039 1103 0\n2047 -58 -41 0 1896 2017 1936 2011 2020 2013 2014 48 47 46 98 2045 1559 1356 1730 1713 743 774 750 771 755 737 696 133 1449 2046 237 1408 2039 0\n2048 -175 -41 0 2022 2047 205 736 1920 1779 1382 107 1332 0\n2049 -89 -41 0 1896 2020 2021 1793 2011 2014 2048 756 1679 788 774 771 2047 205 48 755 750 743 708 1779 735 228 412 696 133 731 1639 1392 185 741 157 703 4 161 55 45 510 1642 419 1559 160 365 1624 769 235 237 239 267 883 727 0\n2050 -41 0 2020 2011 2021 2013 2014 2017 1896 48 205 2047 2048 756 755 1679 750 788 741 743 774 708 769 771 157 185 228 1779 703 412 735 4 696 133 1392 2049 170 1449 1751 727 95 0\n2051 -72 -33 58 0 2020 2017 1896 2021 1936 2050 107 1920 756 1679 784 765 755 750 741 22 185 228 1779 703 412 735 29 696 717 128 0\n2052 -33 58 0 2020 2017 2011 1936 107 1920 756 755 1679 750 788 784 743 774 765 769 2051 1745 25 59 171 191 212 727 0\n2053 -36 58 0 2020 2052 25 59 122 128 171 191 212 1811 727 0\n2054 66 58 0 1896 2017 2020 1936 2053 2052 1559 1812 1459 1679 737 784 755 765 750 1745 743 0\n2055 58 0 1896 2011 1793 1936 2050 2017 2052 1552 1559 2053 1713 774 771 2054 133 1822 731 717 209 765 708 784 743 1679 750 760 0\n2056 -21 0 2055 97 0\n2057 -26 0 2055 98 0\n2058 -49 0 2055 99 0\n2059 -57 0 2055 103 0\n2060 -71 0 2056 505 0\n2061 180 36 33 0 2020 2017 2050 1936 1896 2022 1559 1713 760 755 1679 737 784 765 717 1745 30 1822 743 1557 696 746 1334 0\n2062 36 33 0 1896 2011 1936 1793 2017 1559 1552 1713 774 771 2061 750 743 708 1745 209 765 731 784 133 1679 1812 0\n2063 33 0 2057 2011 2062 59 128 171 191 212 1812 727 1679 769 788 774 0\n2064 -24 0 2063 21 0\n2065 -30 0 2063 22 0\n2066 -42 0 2063 53 0\n2067 -53 0 2063 81 0\n2068 -73 0 2063 163 0\n2069 89 -36 0 1793 2068 2050 2016 1896 2065 2057 2011 2013 2015 2059 2055 2063 191 59 171 212 727 769 774 788 1679 760 750 741 718 1939 743 128 756 737 696 241 1624 708 33 703 417 412 1677 763 122 767 731 200 1597 400 1618 1646 712 1180 0\n2070 -36 0 2059 2015 2050 2057 2016 2011 1793 2068 2065 2012 1896 2055 2063 59 122 128 171 191 212 718 400 1597 1939 727 769 767 774 731 788 1679 756 760 737 750 696 741 743 241 412 417 1624 708 33 703 2069 233 1569 1546 1008 0\n2071 -67 -82 -39 0 2064 2011 2057 2059 2050 1936 2017 1896 2065 2068 2070 2058 2014 2056 2055 2063 33 35 717 765 784 1679 760 750 741 703 187 158 1715 201 1471 1713 774 769 219 727 58 712 1541 1639 199 1564 412 417 1596 1164 0\n2072 -86 -82 -39 0 2064 2056 2014 2011 2057 2059 1896 2065 2070 2050 1936 2017 2055 2063 35 717 765 784 1679 756 737 2071 696 380 33 760 750 741 703 187 158 1715 201 1471 1713 774 769 219 727 58 712 1541 1639 1564 534 1086 0\n2073 90 -82 -39 0 2064 2056 2014 2011 2057 2059 1896 2065 2070 2050 1936 2017 2058 2060 2055 2063 2072 35 717 765 784 1679 756 737 2071 696 380 33 760 750 741 703 187 158 1715 201 1471 1713 774 769 219 727 58 712 1541 1639 1564 1652 375 1094 0\n2074 -82 -39 0 2064 2056 2011 2070 2050 1936 2017 2065 2014 2057 1896 2059 2055 2063 33 35 717 765 784 1679 760 750 741 703 187 158 1715 1471 756 737 1713 774 769 1564 201 219 1639 727 58 1541 712 2071 380 696 2073 536 1122 0\n2075 -89 -39 0 2064 2056 2059 2065 1793 2011 2070 2050 1936 2017 2068 2012 1896 2057 2055 2063 35 717 765 784 1679 756 737 158 1713 774 771 2074 731 133 696 417 412 124 33 760 750 741 703 1715 1471 769 1564 233 239 1647 1567 1546 727 1178 0\n2076 84 -39 0 2064 2056 1793 2011 2068 2013 2059 2070 2050 1936 2017 1896 2065 2057 2012 2055 2063 33 35 717 765 784 1679 760 750 741 703 187 158 1715 2075 712 1618 756 737 1713 774 771 2074 731 133 696 417 412 124 1471 769 1564 727 1613 1603 1190 0\n2077 -39 0 2056 2064 2050 1936 2070 2011 2017 2065 1896 1793 2068 2013 2059 2014 2055 2063 33 35 158 204 1564 717 1713 1715 765 774 784 771 1679 756 760 737 750 741 703 187 2074 731 133 696 412 417 2075 1618 712 2076 1663 1637 1186 0\n2078 4 0 2077 2050 2063 1551 0\n2079 96 0 2078 545 0\n2080 -3 89 -65 -78 0 2011 2013 2059 1936 2050 2070 2017 2068 2077 1793 2014 2057 2063 2055 2078 187 185 1715 712 1618 133 124 1713 774 769 186 26 717 765 784 1679 756 760 737 750 696 743 412 417 708 208 1640 727 1185 0\n2081 89 -65 -78 0 2017 2070 2011 2013 2059 1936 2050 1793 2060 2057 2020 2068 2055 2063 2078 133 124 185 1713 774 769 1715 187 186 1618 712 2080 1574 322 467 1466 1629 727 743 750 755 737 696 412 417 1187 0\n2082 -78 82 0 2070 2011 1793 2012 1896 2055 2057 1936 2050 2079 181 185 186 1713 774 769 771 731 124 2081 233 239 1647 1586 1546 727 567 547 539 322 653 578 573 543 667 583 672 591 1672 630 0\n2083 185 45 -89 82 0 2017 2011 2057 1793 2077 239 237 1677 784 774 1679 769 771 756 760 727 731 737 750 208 133 696 743 241 708 1624 0\n2084 45 -89 82 0 1936 2070 2016 2050 2065 1896 2057 2077 239 237 2082 2083 765 717 1939 29 192 703 727 1973 0\n2085 189 78 0 1936 2050 2070 2065 1896 788 1677 1679 765 760 717 750 29 741 703 0\n2086 82 0 2011 1793 2059 2065 1896 2023 2070 1936 2017 2082 2085 774 771 731 124 133 2084 1751 737 696 241 1624 1715 1710 703 741 739 750 1745 760 765 1679 784 0\n2087 -38 0 2086 196 0\n2088 -77 0 2086 200 0\n2089 -80 0 2086 201 0\n2090 -83 0 2086 209 0\n2091 -84 0 2086 219 0\n2092 19 0 2086 2014 1639 0\n2093 3 0 2086 2050 2070 323 0\n2094 -170 0 2087 2070 2050 1936 717 0\n2095 -185 0 2094 765 0\n2096 169 0 2094 2019 762 0\n2097 189 0 2095 1677 0\n2098 -192 0 2095 2017 784 0\n2099 187 0 2097 2011 774 0\n2100 183 0 2098 1679 0\n2101 172 0 2099 769 0\n2102 175 0 2100 756 0\n2103 180 0 2100 760 0\n2104 165 0 2102 737 0\n2105 177 0 2103 750 0\n2106 167 0 2105 741 0\n2107 168 0 2105 743 0\n2108 -74 0 2106 2096 2059 2065 1471 0\n2109 72 0 2107 2077 2090 708 0\n2110 45 0 2108 2101 2089 2057 2091 727 0\n2111 -78 0 2109 185 0\n2112 -86 0 2109 228 0\n2113 90 0 2109 1624 0\n2114 92 0 2109 1642 0\n2115 -31 0 2110 58 0\n2116 28 0 2111 1896 2065 2106 703 0\n2117 -67 0 2112 412 0\n2118 11 0 2114 2068 2066 2067 419 0\n2119 89 0 2115 2059 2096 2088 712 0\n2120 66 0 2117 2104 696 0\n2121 0 2118 2120 2093 2116 2078 2063 2086 2055 2092 2109 2110 2119 2113 2114 1124 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.l) :=
(.branch 158
 (.branch 79
 (.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 3
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
 (.branch 6
 (.branch 5
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))
 (.branch 7
 (.leaf (⟨6, by decide⟩))
 (.branch 8
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨8, by decide⟩))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨10, by decide⟩)))
 (.branch 12
 (.leaf (⟨11, by decide⟩))
 (.branch 13
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨13, by decide⟩)))))
 (.branch 16
 (.branch 15
 (.leaf (⟨14, by decide⟩))
 (.leaf (⟨15, by decide⟩)))
 (.branch 17
 (.leaf (⟨16, by decide⟩))
 (.branch 18
 (.leaf (⟨17, by decide⟩))
 (.leaf (⟨18, by decide⟩)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (⟨19, by decide⟩))
 (.leaf (⟨20, by decide⟩)))
 (.branch 22
 (.leaf (⟨21, by decide⟩))
 (.branch 23
 (.leaf (⟨22, by decide⟩))
 (.leaf (⟨23, by decide⟩)))))
 (.branch 26
 (.branch 25
 (.leaf (⟨24, by decide⟩))
 (.leaf (⟨25, by decide⟩)))
 (.branch 27
 (.leaf (⟨26, by decide⟩))
 (.branch 28
 (.leaf (⟨27, by decide⟩))
 (.leaf (⟨28, by decide⟩))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (⟨29, by decide⟩))
 (.leaf (⟨30, by decide⟩)))
 (.branch 32
 (.leaf (⟨31, by decide⟩))
 (.branch 33
 (.leaf (⟨32, by decide⟩))
 (.leaf (⟨33, by decide⟩)))))
 (.branch 36
 (.branch 35
 (.leaf (⟨34, by decide⟩))
 (.leaf (⟨35, by decide⟩)))
 (.branch 37
 (.leaf (⟨36, by decide⟩))
 (.branch 38
 (.leaf (⟨37, by decide⟩))
 (.leaf (⟨38, by decide⟩))))))))
 (.branch 59
 (.branch 49
 (.branch 44
 (.branch 41
 (.branch 40
 (.leaf (⟨39, by decide⟩))
 (.leaf (⟨40, by decide⟩)))
 (.branch 42
 (.leaf (⟨41, by decide⟩))
 (.branch 43
 (.leaf (⟨42, by decide⟩))
 (.leaf (⟨43, by decide⟩)))))
 (.branch 46
 (.branch 45
 (.leaf (⟨44, by decide⟩))
 (.leaf (⟨45, by decide⟩)))
 (.branch 47
 (.leaf (⟨46, by decide⟩))
 (.branch 48
 (.leaf (⟨47, by decide⟩))
 (.leaf (⟨48, by decide⟩))))))
 (.branch 54
 (.branch 51
 (.branch 50
 (.leaf (⟨49, by decide⟩))
 (.leaf (⟨50, by decide⟩)))
 (.branch 52
 (.leaf (⟨51, by decide⟩))
 (.branch 53
 (.leaf (⟨52, by decide⟩))
 (.leaf (⟨53, by decide⟩)))))
 (.branch 56
 (.branch 55
 (.leaf (⟨54, by decide⟩))
 (.leaf (⟨55, by decide⟩)))
 (.branch 57
 (.leaf (⟨56, by decide⟩))
 (.branch 58
 (.leaf (⟨57, by decide⟩))
 (.leaf (⟨58, by decide⟩)))))))
 (.branch 69
 (.branch 64
 (.branch 61
 (.branch 60
 (.leaf (⟨59, by decide⟩))
 (.leaf (⟨60, by decide⟩)))
 (.branch 62
 (.leaf (⟨61, by decide⟩))
 (.branch 63
 (.leaf (⟨62, by decide⟩))
 (.leaf (⟨63, by decide⟩)))))
 (.branch 66
 (.branch 65
 (.leaf (⟨64, by decide⟩))
 (.leaf (⟨65, by decide⟩)))
 (.branch 67
 (.leaf (⟨66, by decide⟩))
 (.branch 68
 (.leaf (⟨67, by decide⟩))
 (.leaf (⟨68, by decide⟩))))))
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf (⟨69, by decide⟩))
 (.leaf (⟨70, by decide⟩)))
 (.branch 72
 (.leaf (⟨71, by decide⟩))
 (.branch 73
 (.leaf (⟨72, by decide⟩))
 (.leaf (⟨73, by decide⟩)))))
 (.branch 76
 (.branch 75
 (.leaf (⟨74, by decide⟩))
 (.leaf (⟨75, by decide⟩)))
 (.branch 77
 (.leaf (⟨76, by decide⟩))
 (.branch 78
 (.leaf (⟨77, by decide⟩))
 (.leaf (⟨78, by decide⟩)))))))))
 (.branch 118
 (.branch 98
 (.branch 88
 (.branch 83
 (.branch 81
 (.branch 80
 (.leaf (⟨79, by decide⟩))
 (.leaf (⟨80, by decide⟩)))
 (.branch 82
 (.leaf (⟨81, by decide⟩))
 (.leaf (⟨82, by decide⟩))))
 (.branch 85
 (.branch 84
 (.leaf (⟨83, by decide⟩))
 (.leaf (⟨84, by decide⟩)))
 (.branch 86
 (.leaf (⟨85, by decide⟩))
 (.branch 87
 (.leaf (⟨86, by decide⟩))
 (.leaf (⟨87, by decide⟩))))))
 (.branch 93
 (.branch 90
 (.branch 89
 (.leaf (⟨88, by decide⟩))
 (.leaf (⟨89, by decide⟩)))
 (.branch 91
 (.leaf (⟨90, by decide⟩))
 (.branch 92
 (.leaf (⟨91, by decide⟩))
 (.leaf (⟨92, by decide⟩)))))
 (.branch 95
 (.branch 94
 (.leaf (⟨93, by decide⟩))
 (.leaf (⟨94, by decide⟩)))
 (.branch 96
 (.leaf (⟨95, by decide⟩))
 (.branch 97
 (.leaf (⟨96, by decide⟩))
 (.leaf (⟨97, by decide⟩)))))))
 (.branch 108
 (.branch 103
 (.branch 100
 (.branch 99
 (.leaf (⟨98, by decide⟩))
 (.leaf (⟨99, by decide⟩)))
 (.branch 101
 (.leaf (⟨100, by decide⟩))
 (.branch 102
 (.leaf (⟨101, by decide⟩))
 (.leaf (⟨102, by decide⟩)))))
 (.branch 105
 (.branch 104
 (.leaf (⟨103, by decide⟩))
 (.leaf (⟨104, by decide⟩)))
 (.branch 106
 (.leaf (⟨105, by decide⟩))
 (.branch 107
 (.leaf (⟨106, by decide⟩))
 (.leaf (⟨107, by decide⟩))))))
 (.branch 113
 (.branch 110
 (.branch 109
 (.leaf (⟨108, by decide⟩))
 (.leaf (⟨109, by decide⟩)))
 (.branch 111
 (.leaf (⟨110, by decide⟩))
 (.branch 112
 (.leaf (⟨111, by decide⟩))
 (.leaf (⟨112, by decide⟩)))))
 (.branch 115
 (.branch 114
 (.leaf (⟨113, by decide⟩))
 (.leaf (⟨114, by decide⟩)))
 (.branch 116
 (.leaf (⟨115, by decide⟩))
 (.branch 117
 (.leaf (⟨116, by decide⟩))
 (.leaf (⟨117, by decide⟩))))))))
 (.branch 138
 (.branch 128
 (.branch 123
 (.branch 120
 (.branch 119
 (.leaf (⟨118, by decide⟩))
 (.leaf (⟨119, by decide⟩)))
 (.branch 121
 (.leaf (⟨120, by decide⟩))
 (.branch 122
 (.leaf (⟨121, by decide⟩))
 (.leaf (⟨122, by decide⟩)))))
 (.branch 125
 (.branch 124
 (.leaf (⟨123, by decide⟩))
 (.leaf (⟨124, by decide⟩)))
 (.branch 126
 (.leaf (⟨125, by decide⟩))
 (.branch 127
 (.leaf (⟨126, by decide⟩))
 (.leaf (⟨127, by decide⟩))))))
 (.branch 133
 (.branch 130
 (.branch 129
 (.leaf (⟨128, by decide⟩))
 (.leaf (⟨129, by decide⟩)))
 (.branch 131
 (.leaf (⟨130, by decide⟩))
 (.branch 132
 (.leaf (⟨131, by decide⟩))
 (.leaf (⟨132, by decide⟩)))))
 (.branch 135
 (.branch 134
 (.leaf (⟨133, by decide⟩))
 (.leaf (⟨134, by decide⟩)))
 (.branch 136
 (.leaf (⟨135, by decide⟩))
 (.branch 137
 (.leaf (⟨136, by decide⟩))
 (.leaf (⟨137, by decide⟩)))))))
 (.branch 148
 (.branch 143
 (.branch 140
 (.branch 139
 (.leaf (⟨138, by decide⟩))
 (.leaf (⟨139, by decide⟩)))
 (.branch 141
 (.leaf (⟨140, by decide⟩))
 (.branch 142
 (.leaf (⟨141, by decide⟩))
 (.leaf (⟨142, by decide⟩)))))
 (.branch 145
 (.branch 144
 (.leaf (⟨143, by decide⟩))
 (.leaf (⟨144, by decide⟩)))
 (.branch 146
 (.leaf (⟨145, by decide⟩))
 (.branch 147
 (.leaf (⟨146, by decide⟩))
 (.leaf (⟨147, by decide⟩))))))
 (.branch 153
 (.branch 150
 (.branch 149
 (.leaf (⟨148, by decide⟩))
 (.leaf (⟨149, by decide⟩)))
 (.branch 151
 (.leaf (⟨150, by decide⟩))
 (.branch 152
 (.leaf (⟨151, by decide⟩))
 (.leaf (⟨152, by decide⟩)))))
 (.branch 155
 (.branch 154
 (.leaf (⟨153, by decide⟩))
 (.leaf (⟨154, by decide⟩)))
 (.branch 156
 (.leaf (⟨155, by decide⟩))
 (.branch 157
 (.leaf (⟨156, by decide⟩))
 (.leaf (⟨157, by decide⟩))))))))))
 (.branch 237
 (.branch 197
 (.branch 177
 (.branch 167
 (.branch 162
 (.branch 160
 (.branch 159
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 161
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
 (.branch 164
 (.branch 163
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))
 (.branch 165
 (.leaf (⟨6, by decide⟩))
 (.branch 166
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨8, by decide⟩))))))
 (.branch 172
 (.branch 169
 (.branch 168
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨10, by decide⟩)))
 (.branch 170
 (.leaf (⟨11, by decide⟩))
 (.branch 171
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨13, by decide⟩)))))
 (.branch 174
 (.branch 173
 (.leaf (⟨14, by decide⟩))
 (.leaf (⟨15, by decide⟩)))
 (.branch 175
 (.leaf (⟨16, by decide⟩))
 (.branch 176
 (.leaf (⟨17, by decide⟩))
 (.leaf (⟨18, by decide⟩)))))))
 (.branch 187
 (.branch 182
 (.branch 179
 (.branch 178
 (.leaf (⟨19, by decide⟩))
 (.leaf (⟨20, by decide⟩)))
 (.branch 180
 (.leaf (⟨21, by decide⟩))
 (.branch 181
 (.leaf (⟨22, by decide⟩))
 (.leaf (⟨23, by decide⟩)))))
 (.branch 184
 (.branch 183
 (.leaf (⟨24, by decide⟩))
 (.leaf (⟨25, by decide⟩)))
 (.branch 185
 (.leaf (⟨26, by decide⟩))
 (.branch 186
 (.leaf (⟨27, by decide⟩))
 (.leaf (⟨28, by decide⟩))))))
 (.branch 192
 (.branch 189
 (.branch 188
 (.leaf (⟨29, by decide⟩))
 (.leaf (⟨30, by decide⟩)))
 (.branch 190
 (.leaf (⟨31, by decide⟩))
 (.branch 191
 (.leaf (⟨32, by decide⟩))
 (.leaf (⟨33, by decide⟩)))))
 (.branch 194
 (.branch 193
 (.leaf (⟨34, by decide⟩))
 (.leaf (⟨35, by decide⟩)))
 (.branch 195
 (.leaf (⟨36, by decide⟩))
 (.branch 196
 (.leaf (⟨37, by decide⟩))
 (.leaf (⟨38, by decide⟩))))))))
 (.branch 217
 (.branch 207
 (.branch 202
 (.branch 199
 (.branch 198
 (.leaf (⟨39, by decide⟩))
 (.leaf (⟨40, by decide⟩)))
 (.branch 200
 (.leaf (⟨41, by decide⟩))
 (.branch 201
 (.leaf (⟨42, by decide⟩))
 (.leaf (⟨43, by decide⟩)))))
 (.branch 204
 (.branch 203
 (.leaf (⟨44, by decide⟩))
 (.leaf (⟨45, by decide⟩)))
 (.branch 205
 (.leaf (⟨46, by decide⟩))
 (.branch 206
 (.leaf (⟨47, by decide⟩))
 (.leaf (⟨48, by decide⟩))))))
 (.branch 212
 (.branch 209
 (.branch 208
 (.leaf (⟨49, by decide⟩))
 (.leaf (⟨50, by decide⟩)))
 (.branch 210
 (.leaf (⟨51, by decide⟩))
 (.branch 211
 (.leaf (⟨52, by decide⟩))
 (.leaf (⟨53, by decide⟩)))))
 (.branch 214
 (.branch 213
 (.leaf (⟨54, by decide⟩))
 (.leaf (⟨55, by decide⟩)))
 (.branch 215
 (.leaf (⟨56, by decide⟩))
 (.branch 216
 (.leaf (⟨57, by decide⟩))
 (.leaf (⟨58, by decide⟩)))))))
 (.branch 227
 (.branch 222
 (.branch 219
 (.branch 218
 (.leaf (⟨59, by decide⟩))
 (.leaf (⟨60, by decide⟩)))
 (.branch 220
 (.leaf (⟨61, by decide⟩))
 (.branch 221
 (.leaf (⟨62, by decide⟩))
 (.leaf (⟨63, by decide⟩)))))
 (.branch 224
 (.branch 223
 (.leaf (⟨64, by decide⟩))
 (.leaf (⟨65, by decide⟩)))
 (.branch 225
 (.leaf (⟨66, by decide⟩))
 (.branch 226
 (.leaf (⟨67, by decide⟩))
 (.leaf (⟨68, by decide⟩))))))
 (.branch 232
 (.branch 229
 (.branch 228
 (.leaf (⟨69, by decide⟩))
 (.leaf (⟨70, by decide⟩)))
 (.branch 230
 (.leaf (⟨71, by decide⟩))
 (.branch 231
 (.leaf (⟨72, by decide⟩))
 (.leaf (⟨73, by decide⟩)))))
 (.branch 234
 (.branch 233
 (.leaf (⟨74, by decide⟩))
 (.leaf (⟨75, by decide⟩)))
 (.branch 235
 (.leaf (⟨76, by decide⟩))
 (.branch 236
 (.leaf (⟨77, by decide⟩))
 (.leaf (⟨78, by decide⟩)))))))))
 (.branch 276
 (.branch 256
 (.branch 246
 (.branch 241
 (.branch 239
 (.branch 238
 (.leaf (⟨79, by decide⟩))
 (.leaf (⟨80, by decide⟩)))
 (.branch 240
 (.leaf (⟨81, by decide⟩))
 (.leaf (⟨82, by decide⟩))))
 (.branch 243
 (.branch 242
 (.leaf (⟨83, by decide⟩))
 (.leaf (⟨84, by decide⟩)))
 (.branch 244
 (.leaf (⟨85, by decide⟩))
 (.branch 245
 (.leaf (⟨86, by decide⟩))
 (.leaf (⟨87, by decide⟩))))))
 (.branch 251
 (.branch 248
 (.branch 247
 (.leaf (⟨88, by decide⟩))
 (.leaf (⟨89, by decide⟩)))
 (.branch 249
 (.leaf (⟨90, by decide⟩))
 (.branch 250
 (.leaf (⟨91, by decide⟩))
 (.leaf (⟨92, by decide⟩)))))
 (.branch 253
 (.branch 252
 (.leaf (⟨93, by decide⟩))
 (.leaf (⟨94, by decide⟩)))
 (.branch 254
 (.leaf (⟨95, by decide⟩))
 (.branch 255
 (.leaf (⟨96, by decide⟩))
 (.leaf (⟨97, by decide⟩)))))))
 (.branch 266
 (.branch 261
 (.branch 258
 (.branch 257
 (.leaf (⟨98, by decide⟩))
 (.leaf (⟨99, by decide⟩)))
 (.branch 259
 (.leaf (⟨100, by decide⟩))
 (.branch 260
 (.leaf (⟨101, by decide⟩))
 (.leaf (⟨102, by decide⟩)))))
 (.branch 263
 (.branch 262
 (.leaf (⟨103, by decide⟩))
 (.leaf (⟨104, by decide⟩)))
 (.branch 264
 (.leaf (⟨105, by decide⟩))
 (.branch 265
 (.leaf (⟨106, by decide⟩))
 (.leaf (⟨107, by decide⟩))))))
 (.branch 271
 (.branch 268
 (.branch 267
 (.leaf (⟨108, by decide⟩))
 (.leaf (⟨109, by decide⟩)))
 (.branch 269
 (.leaf (⟨110, by decide⟩))
 (.branch 270
 (.leaf (⟨111, by decide⟩))
 (.leaf (⟨112, by decide⟩)))))
 (.branch 273
 (.branch 272
 (.leaf (⟨113, by decide⟩))
 (.leaf (⟨114, by decide⟩)))
 (.branch 274
 (.leaf (⟨115, by decide⟩))
 (.branch 275
 (.leaf (⟨116, by decide⟩))
 (.leaf (⟨117, by decide⟩))))))))
 (.branch 296
 (.branch 286
 (.branch 281
 (.branch 278
 (.branch 277
 (.leaf (⟨118, by decide⟩))
 (.leaf (⟨119, by decide⟩)))
 (.branch 279
 (.leaf (⟨120, by decide⟩))
 (.branch 280
 (.leaf (⟨121, by decide⟩))
 (.leaf (⟨122, by decide⟩)))))
 (.branch 283
 (.branch 282
 (.leaf (⟨123, by decide⟩))
 (.leaf (⟨124, by decide⟩)))
 (.branch 284
 (.leaf (⟨125, by decide⟩))
 (.branch 285
 (.leaf (⟨126, by decide⟩))
 (.leaf (⟨127, by decide⟩))))))
 (.branch 291
 (.branch 288
 (.branch 287
 (.leaf (⟨128, by decide⟩))
 (.leaf (⟨129, by decide⟩)))
 (.branch 289
 (.leaf (⟨130, by decide⟩))
 (.branch 290
 (.leaf (⟨131, by decide⟩))
 (.leaf (⟨132, by decide⟩)))))
 (.branch 293
 (.branch 292
 (.leaf (⟨133, by decide⟩))
 (.leaf (⟨134, by decide⟩)))
 (.branch 294
 (.leaf (⟨135, by decide⟩))
 (.branch 295
 (.leaf (⟨136, by decide⟩))
 (.leaf (⟨137, by decide⟩)))))))
 (.branch 306
 (.branch 301
 (.branch 298
 (.branch 297
 (.leaf (⟨138, by decide⟩))
 (.leaf (⟨139, by decide⟩)))
 (.branch 299
 (.leaf (⟨140, by decide⟩))
 (.branch 300
 (.leaf (⟨141, by decide⟩))
 (.leaf (⟨142, by decide⟩)))))
 (.branch 303
 (.branch 302
 (.leaf (⟨143, by decide⟩))
 (.leaf (⟨144, by decide⟩)))
 (.branch 304
 (.leaf (⟨145, by decide⟩))
 (.branch 305
 (.leaf (⟨146, by decide⟩))
 (.leaf (⟨147, by decide⟩))))))
 (.branch 311
 (.branch 308
 (.branch 307
 (.leaf (⟨148, by decide⟩))
 (.leaf (⟨149, by decide⟩)))
 (.branch 309
 (.leaf (⟨150, by decide⟩))
 (.branch 310
 (.leaf (⟨151, by decide⟩))
 (.leaf (⟨152, by decide⟩)))))
 (.branch 313
 (.branch 312
 (.leaf (⟨153, by decide⟩))
 (.leaf (⟨154, by decide⟩)))
 (.branch 314
 (.leaf (⟨155, by decide⟩))
 (.branch 315
 (.leaf (⟨156, by decide⟩))
 (.leaf (⟨157, by decide⟩)))))))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.g)) :=
(.branch 158
 (.branch 79
 (.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([]))
 (.leaf ([])))
 (.branch 3
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 6
 (.branch 5
 (.leaf ([]))
 (.leaf ([])))
 (.branch 7
 (.leaf ([]))
 (.branch 8
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ([]))
 (.leaf ([])))
 (.branch 12
 (.leaf ([]))
 (.branch 13
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 16
 (.branch 15
 (.leaf ([]))
 (.leaf ([])))
 (.branch 17
 (.leaf ([]))
 (.branch 18
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ([]))
 (.leaf ([])))
 (.branch 22
 (.leaf ([]))
 (.branch 23
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 26
 (.branch 25
 (.leaf ([]))
 (.leaf ([])))
 (.branch 27
 (.leaf ([]))
 (.branch 28
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ([]))
 (.leaf ([])))
 (.branch 32
 (.leaf ([]))
 (.branch 33
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 36
 (.branch 35
 (.leaf ([]))
 (.leaf ([])))
 (.branch 37
 (.leaf ([]))
 (.branch 38
 (.leaf ([]))
 (.leaf ([]))))))))
 (.branch 59
 (.branch 49
 (.branch 44
 (.branch 41
 (.branch 40
 (.leaf ([]))
 (.leaf ([])))
 (.branch 42
 (.leaf ([]))
 (.branch 43
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 46
 (.branch 45
 (.leaf ([]))
 (.leaf ([])))
 (.branch 47
 (.leaf ([]))
 (.branch 48
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 54
 (.branch 51
 (.branch 50
 (.leaf ([]))
 (.leaf ([])))
 (.branch 52
 (.leaf ([]))
 (.branch 53
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 56
 (.branch 55
 (.leaf ([]))
 (.leaf ([])))
 (.branch 57
 (.leaf ([]))
 (.branch 58
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 69
 (.branch 64
 (.branch 61
 (.branch 60
 (.leaf ([]))
 (.leaf ([])))
 (.branch 62
 (.leaf ([]))
 (.branch 63
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 66
 (.branch 65
 (.leaf ([]))
 (.leaf ([])))
 (.branch 67
 (.leaf ([]))
 (.branch 68
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf ([]))
 (.leaf ([])))
 (.branch 72
 (.leaf ([]))
 (.branch 73
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 76
 (.branch 75
 (.leaf ([]))
 (.leaf ([])))
 (.branch 77
 (.leaf ([]))
 (.branch 78
 (.leaf ([]))
 (.leaf ([])))))))))
 (.branch 118
 (.branch 98
 (.branch 88
 (.branch 83
 (.branch 81
 (.branch 80
 (.leaf ([]))
 (.leaf ([])))
 (.branch 82
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 85
 (.branch 84
 (.leaf ([]))
 (.leaf ([])))
 (.branch 86
 (.leaf ([]))
 (.branch 87
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 93
 (.branch 90
 (.branch 89
 (.leaf ([]))
 (.leaf ([])))
 (.branch 91
 (.leaf ([]))
 (.branch 92
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 95
 (.branch 94
 (.leaf ([]))
 (.leaf ([])))
 (.branch 96
 (.leaf ([]))
 (.branch 97
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 108
 (.branch 103
 (.branch 100
 (.branch 99
 (.leaf ([]))
 (.leaf ([])))
 (.branch 101
 (.leaf ([]))
 (.branch 102
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 105
 (.branch 104
 (.leaf ([]))
 (.leaf ([])))
 (.branch 106
 (.leaf ([]))
 (.branch 107
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 113
 (.branch 110
 (.branch 109
 (.leaf ([]))
 (.leaf ([])))
 (.branch 111
 (.leaf ([]))
 (.branch 112
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 115
 (.branch 114
 (.leaf ([]))
 (.leaf ([])))
 (.branch 116
 (.leaf ([]))
 (.branch 117
 (.leaf ([]))
 (.leaf ([]))))))))
 (.branch 138
 (.branch 128
 (.branch 123
 (.branch 120
 (.branch 119
 (.leaf ([]))
 (.leaf ([])))
 (.branch 121
 (.leaf ([]))
 (.branch 122
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 125
 (.branch 124
 (.leaf ([]))
 (.leaf ([])))
 (.branch 126
 (.leaf ([]))
 (.branch 127
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 133
 (.branch 130
 (.branch 129
 (.leaf ([]))
 (.leaf ([])))
 (.branch 131
 (.leaf ([]))
 (.branch 132
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 135
 (.branch 134
 (.leaf ([]))
 (.leaf ([])))
 (.branch 136
 (.leaf ([]))
 (.branch 137
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 148
 (.branch 143
 (.branch 140
 (.branch 139
 (.leaf ([]))
 (.leaf ([])))
 (.branch 141
 (.leaf ([]))
 (.branch 142
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 145
 (.branch 144
 (.leaf ([]))
 (.leaf ([])))
 (.branch 146
 (.leaf ([]))
 (.branch 147
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 153
 (.branch 150
 (.branch 149
 (.leaf ([]))
 (.leaf ([])))
 (.branch 151
 (.leaf ([]))
 (.branch 152
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 155
 (.branch 154
 (.leaf ([]))
 (.leaf ([])))
 (.branch 156
 (.leaf ([]))
 (.branch 157
 (.leaf ([]))
 (.leaf ([]))))))))))
 (.branch 237
 (.branch 197
 (.branch 177
 (.branch 167
 (.branch 162
 (.branch 160
 (.branch 159
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 161
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 164
 (.branch 163
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 165
 (.leaf ([⟨1, by decide⟩]))
 (.branch 166
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 172
 (.branch 169
 (.branch 168
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 170
 (.leaf ([⟨1, by decide⟩]))
 (.branch 171
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 174
 (.branch 173
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 175
 (.leaf ([⟨1, by decide⟩]))
 (.branch 176
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))
 (.branch 187
 (.branch 182
 (.branch 179
 (.branch 178
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 180
 (.leaf ([⟨1, by decide⟩]))
 (.branch 181
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 184
 (.branch 183
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 185
 (.leaf ([⟨1, by decide⟩]))
 (.branch 186
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 192
 (.branch 189
 (.branch 188
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 190
 (.leaf ([⟨1, by decide⟩]))
 (.branch 191
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 194
 (.branch 193
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 195
 (.leaf ([⟨1, by decide⟩]))
 (.branch 196
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))))
 (.branch 217
 (.branch 207
 (.branch 202
 (.branch 199
 (.branch 198
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 200
 (.leaf ([⟨1, by decide⟩]))
 (.branch 201
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 204
 (.branch 203
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 205
 (.leaf ([⟨1, by decide⟩]))
 (.branch 206
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 212
 (.branch 209
 (.branch 208
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 210
 (.leaf ([⟨1, by decide⟩]))
 (.branch 211
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 214
 (.branch 213
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 215
 (.leaf ([⟨1, by decide⟩]))
 (.branch 216
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))
 (.branch 227
 (.branch 222
 (.branch 219
 (.branch 218
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 220
 (.leaf ([⟨1, by decide⟩]))
 (.branch 221
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 224
 (.branch 223
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 225
 (.leaf ([⟨1, by decide⟩]))
 (.branch 226
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 232
 (.branch 229
 (.branch 228
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 230
 (.leaf ([⟨1, by decide⟩]))
 (.branch 231
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 234
 (.branch 233
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 235
 (.leaf ([⟨1, by decide⟩]))
 (.branch 236
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))))
 (.branch 276
 (.branch 256
 (.branch 246
 (.branch 241
 (.branch 239
 (.branch 238
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 240
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 243
 (.branch 242
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 244
 (.leaf ([⟨1, by decide⟩]))
 (.branch 245
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 251
 (.branch 248
 (.branch 247
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 249
 (.leaf ([⟨1, by decide⟩]))
 (.branch 250
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 253
 (.branch 252
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 254
 (.leaf ([⟨1, by decide⟩]))
 (.branch 255
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))
 (.branch 266
 (.branch 261
 (.branch 258
 (.branch 257
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 259
 (.leaf ([⟨1, by decide⟩]))
 (.branch 260
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 263
 (.branch 262
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 264
 (.leaf ([⟨1, by decide⟩]))
 (.branch 265
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 271
 (.branch 268
 (.branch 267
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 269
 (.leaf ([⟨1, by decide⟩]))
 (.branch 270
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 273
 (.branch 272
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 274
 (.leaf ([⟨1, by decide⟩]))
 (.branch 275
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))))
 (.branch 296
 (.branch 286
 (.branch 281
 (.branch 278
 (.branch 277
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 279
 (.leaf ([⟨1, by decide⟩]))
 (.branch 280
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 283
 (.branch 282
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 284
 (.leaf ([⟨1, by decide⟩]))
 (.branch 285
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 291
 (.branch 288
 (.branch 287
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 289
 (.leaf ([⟨1, by decide⟩]))
 (.branch 290
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 293
 (.branch 292
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 294
 (.leaf ([⟨1, by decide⟩]))
 (.branch 295
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))
 (.branch 306
 (.branch 301
 (.branch 298
 (.branch 297
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 299
 (.leaf ([⟨1, by decide⟩]))
 (.branch 300
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 303
 (.branch 302
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 304
 (.leaf ([⟨1, by decide⟩]))
 (.branch 305
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 311
 (.branch 308
 (.branch 307
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 309
 (.leaf ([⟨1, by decide⟩]))
 (.branch 310
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 313
 (.branch 312
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 314
 (.leaf ([⟨1, by decide⟩]))
 (.branch 315
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007
