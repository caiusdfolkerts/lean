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

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":1},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":3},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0050\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0050\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0059\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0066\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0064\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0060\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0060\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0069\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0069\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0073\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0073\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0070\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0070\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007" 211

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007" "{\"ridges\":[[0,7],[2,131],[3,11],[6,517],[6,532],[7,261],[7,769],[7,772],[9,536],[10,265],[10,776],[12,38],[14,42],[15,290],[17,52],[17,100],[18,168],[20,30],[21,45],[22,261],[23,526],[24,51],[25,7],[25,67],[25,81],[25,84],[26,150],[27,7],[27,38],[27,67],[27,98],[27,100],[28,165],[29,38],[30,7],[30,69],[30,70],[30,131],[30,193],[30,194],[31,67],[31,69],[31,70],[31,259],[31,261],[31,262],[32,7],[32,259],[32,262],[32,517],[32,769],[32,772],[33,51],[34,90],[35,131],[35,145],[35,152],[36,105],[37,11],[37,42],[37,168],[38,11],[38,42],[38,290],[39,11],[39,67],[39,137],[39,138],[39,193],[39,194],[40,131],[40,137],[40,138],[40,259],[40,265],[40,266],[41,259],[41,521],[41,769],[41,776],[42,51],[43,51],[44,67],[44,81],[44,131],[44,194],[45,67],[45,98],[45,131],[45,162],[45,193],[45,224],[46,353],[47,417],[48,45],[50,517],[50,521],[50,532],[50,536],[51,45],[52,261],[52,265],[52,772],[52,776],[53,52],[53,69],[53,81],[53,112],[54,165],[55,305],[56,69],[56,84],[56,193],[56,208],[57,69],[57,81],[57,84],[57,517],[57,529],[57,532],[58,261],[58,529],[58,532],[58,769],[58,772],[59,165],[60,353],[61,105],[62,145],[63,305],[64,137],[64,152],[64,193],[64,208],[65,137],[65,145],[65,152],[65,521],[65,529],[65,536],[66,25],[66,265],[66,529],[66,536],[66,769],[66,776],[67,105],[68,417],[69,112],[69,145],[69,176],[69,193],[69,224],[70,30],[71,38],[71,42],[71,262],[71,266],[71,292],[71,296],[72,526],[73,38],[73,52],[73,70],[73,84],[73,98],[74,150],[75,150],[76,38],[76,70],[76,100],[76,224],[77,70],[77,98],[77,100],[77,262],[77,290],[77,292],[78,90],[79,42],[79,56],[79,162],[79,176],[80,90],[81,42],[81,98],[81,138],[81,168],[81,194],[81,224],[82,138],[82,162],[82,168],[82,266],[82,290],[83,98],[83,112],[83,162],[83,176],[85,52],[85,56],[85,556],[86,284],[87,292],[87,296],[87,556],[87,772],[88,52],[88,84],[88,100],[88,176],[88,208],[88,224],[89,772],[89,816],[90,112],[90,152],[90,168],[90,208],[90,224],[91,56],[91,536],[91,776],[91,816]],\"owners\":[[0,7,[1,20,21,22,23,24,26,28,29,32],[25,27,30]],[25,7,[1,21,22,23,28,29,32],[0,20,24,26,27,30]],[27,7,[1,20,22,23,26,32],[0,21,24,25,28,29,30]],[30,7,[1,20,21,22,23,24,29,32],[0,25,26,27,28]],[32,7,[0,20,21,24,25,26,27,28,30],[1,22,23,29]],[25,67,[4,36,39,45,46],[0,27,31,34,42,44]],[27,67,[4,34,39,44],[0,25,31,36,42,45,46]],[31,67,[4,34,36,39,42,44,45],[0,25,27,46]],[39,67,[0,25,27,31,42,46],[4,34,36,44,45]],[44,67,[0,27,31,36,46],[4,25,34,39,42,45]],[45,67,[0,25,31,34],[4,27,36,39,42,44,46]],[30,69,[5,53,57,60],[0,27,31,56,59]],[31,69,[5,53,56,57,59],[0,27,30,60]],[53,69,[0,30,31],[5,27,56,57,59,60]],[56,69,[0,27,31,60],[5,30,53,57,59]],[57,69,[0,27,30,31,59,60],[5,53,56]],[30,70,[12,73,77],[0,25,31,75,76]],[31,70,[12,73,75,76],[0,25,30,77]],[73,70,[0,30,31],[12,25,75,76,77]],[76,70,[0,25,31],[12,30,73,75,77]],[77,70,[0,25,30,75],[12,31,73,76]],[31,259,[3,38,40,41,47],[1,29,32,46]],[32,259,[3,38,40,46,47],[1,29,31,41]],[40,259,[1,29,31,32,46],[3,38,41,47]],[41,259,[1,29,31,46,47],[3,32,38,40]],[7,261,[1,22,29,31,49,51,55,60],[52,58]],[22,261,[7,55,58,60],[1,29,31,49,51,52]],[31,261,[7,49,51,52,55,58],[1,22,29,60]],[52,261,[1,29,31,55,60],[7,22,49,51,58]],[58,261,[1,22,29,31,51,60],[7,49,52,55]],[31,262,[13,71,72],[1,22,32,77]],[32,262,[13,71,77],[1,22,31,72]],[71,262,[1,31,32],[13,22,72,77]],[77,262,[1,22,32,72],[13,31,71]],[3,11,[2,20,21,23,33,34,35,36,37,39],[22,38,41]],[37,11,[3,20,22,23,34,41],[2,21,33,35,36,38,39]],[38,11,[2,20,23,34,35,39],[3,21,22,33,36,37,41]],[39,11,[3,20,21,22,23,33,38,41],[2,34,35,36,37]],[2,131,[4,26,28,30,43,44,45,47],[35,37,40]],[30,131,[2,35,37,40,43,47],[4,26,28,44,45]],[35,131,[4,28,30,45,47],[2,26,37,40,43,44]],[40,131,[4,26,28,30,43,44,45],[2,35,37,47]],[44,131,[2,28,37,40,47],[4,26,30,35,43,45]],[45,131,[2,26,35,40],[4,28,30,37,43,44,47]],[39,137,[8,62,65,68],[2,37,40,64,67]],[40,137,[8,62,64,65,67],[2,37,39,68]],[64,137,[2,37,40,68],[8,39,62,65,67]],[65,137,[2,37,39,40,67,68],[8,62,64]],[39,138,[14,79,82],[2,35,40,80,81]],[40,138,[14,79,80,81],[2,35,39,82]],[81,138,[2,35,40],[14,39,79,80,82]],[82,138,[2,35,39,80],[14,40,79,81]],[10,265,[3,22,38,40,49,51,63,68],[52,66]],[40,265,[10,49,51,52,63,66],[3,22,38,68]],[52,265,[3,38,40,63,68],[10,22,49,51,66]],[66,265,[3,22,38,40,51,68],[10,49,52,63]],[40,266,[15,71,72],[3,22,41,82]],[71,266,[3,40,41],[15,22,72,82]],[82,266,[3,22,41,72],[15,40,71]],[30,193,[11,64,67,69],[4,39,45,56,59]],[39,193,[11,56,59,69],[4,30,45,64,67]],[45,193,[11,56,64],[4,30,39,59,67,69]],[56,193,[4,39,45,67],[11,30,59,64,69]],[64,193,[4,30,45,59],[11,39,56,67,69]],[69,193,[4,30,39],[11,45,56,59,64,67]],[30,194,[16,80,81,83],[4,39,44,75,76]],[39,194,[16,75,76,83],[4,30,44,80,81]],[44,194,[16,76,81],[4,30,39,75,80,83]],[81,194,[4,30,44,75],[16,39,76,80,83]],[25,81,[11,61,64,69],[5,34,42,44,53,57]],[44,81,[5,53,57,61],[11,25,34,42,64,69]],[53,81,[11,34,44,64],[5,25,42,57,61,69]],[57,81,[11,34,42,44,61,64,69],[5,25,53]],[25,84,[17,88],[5,56,57,73,75]],[56,84,[17,73],[5,25,57,75,88]],[57,84,[17,73,75,88],[5,25,56]],[73,84,[5,56,57],[17,25,75,88]],[88,84,[5,25,57],[17,56,73,75]],[6,517,[7,23,32,52],[50,57]],[32,517,[6,50,57],[7,23,52]],[50,517,[7,32],[6,23,52,57]],[57,517,[7,23,32,52],[6,50]],[57,529,[9,65,66],[6,58]],[58,529,[9,65],[6,57,66]],[65,529,[6,57,58],[9,66]],[66,529,[6,57],[9,58,65]],[6,532,[85,86,89],[50,57,58]],[50,532,[89],[6,57,58,85,86]],[57,532,[85,86,89],[6,50,58]],[58,532,[85],[6,50,57,86,89]],[7,769,[10,41,66],[32,58]],[32,769,[10,66],[7,41,58]],[41,769,[7,58],[10,32,66]],[58,769,[10,41],[7,32,66]],[66,769,[7,32],[10,41,58]],[7,772,[72,86,87,89],[32,52,58]],[32,772,[86,87,89],[7,52,58,72]],[52,772,[89],[7,32,58,72,86,87]],[58,772,[72,87],[7,32,52,86,89]],[87,772,[7,32,58],[52,72,86,89]],[89,772,[7,32,52,72],[58,86,87]],[66,25,[8,20,33,34,35,48,61,62,64],[9,49,50,63]],[35,145,[11,54,56,69],[8,26,43,44,62,65]],[62,145,[11,26,44,56],[8,35,43,54,65,69]],[65,145,[11,26,43,44,54,56,69],[8,35,62]],[69,145,[8,26,35,65],[11,43,44,54,56,62]],[35,152,[18,90],[8,64,65,79,80]],[64,152,[18,79],[8,35,65,80,90]],[65,152,[18,79,80,90],[8,35,64]],[90,152,[8,35,65],[18,64,79,80]],[41,521,[9,50,65],[10,23,52]],[50,521,[10,41],[9,23,52,65]],[65,521,[10,23,41,52],[9,50]],[9,536,[85,86,91],[50,65,66]],[50,536,[91],[9,65,66,85,86]],[65,536,[85,86,91],[9,50,66]],[66,536,[85],[9,50,65,86,91]],[91,536,[9,50,65],[66,85,86]],[10,776,[72,86,87,91],[41,52,66]],[41,776,[86,87,91],[10,52,66,72]],[52,776,[91],[10,41,66,72,86,87]],[66,776,[72,87],[10,41,52,86,91]],[91,776,[10,41,52,72],[66,86,87]],[56,208,[19,80,83,90],[11,44,64,75,88]],[64,208,[19,75,83,88],[11,44,56,80,90]],[88,208,[11,44,64,80],[19,56,75,83,90]],[90,208,[11,44,56,75],[19,64,80,83,88]],[12,38,[13,21,24,28,29,70,71,74],[27,73,76]],[27,38,[13,70,71,74],[12,21,24,28,29,73,76]],[29,38,[12,70,73,74,76],[13,21,24,27,28,71]],[71,38,[12,24,27,28,73,74,76],[13,21,29,70]],[73,38,[13,21,28,29,71],[12,24,27,70,74,76]],[76,38,[13,21,24,29,70,71],[12,27,28,73,74]],[27,98,[16,78,81,83],[12,36,42,45,46,73,77]],[45,98,[12,73,77,78],[16,27,36,42,46,81,83]],[73,98,[16,36,45,46,81],[12,27,42,77,78,83]],[77,98,[16,36,42,45,78,81,83],[12,27,46,73]],[81,98,[12,27,42,46,73,77],[16,36,45,78,83]],[83,98,[12,27,36,46,77],[16,42,45,73,78,81]],[17,100,[12,27,59,60,76,77],[53,88]],[27,100,[17,88],[12,53,59,60,76,77]],[76,100,[17,53,60],[12,27,59,77,88]],[77,100,[17,53,59,88],[12,27,60,76]],[88,100,[12,27,60,77],[17,53,59,76]],[15,290,[13,29,46,47,77],[38,82]],[38,290,[13,77],[15,29,46,47,82]],[77,290,[15,38,47,82],[13,29,46]],[82,290,[13,29,46,77],[15,38,47]],[71,292,[55,60,89],[13,29,51,77,84,87]],[77,292,[51,55,84,87,89],[13,29,60,71]],[87,292,[13,29,55,60,77],[51,71,84,89]],[14,42,[15,21,33,36,38,70,71,78],[37,79,81]],[37,42,[15,70,71,78],[14,21,33,36,38,79,81]],[38,42,[14,70,78,79,81],[15,21,33,36,37,71]],[71,42,[14,33,36,37,78,79,81],[15,21,38,70]],[79,42,[15,21,36,38,71],[14,33,37,70,78,81]],[81,42,[15,21,33,38,70,71],[14,36,37,78,79]],[45,162,[14,74,79,82],[16,28,37,43,47,76,83]],[79,162,[16,28,45,47,76],[14,37,43,74,82,83]],[82,162,[16,28,43,45,74,76,83],[14,37,47,79]],[83,162,[14,28,37,47,82],[16,43,45,74,76,79]],[18,168,[14,37,67,68,81,82],[62,90]],[37,168,[18,90],[14,62,67,68,81,82]],[81,168,[18,62,68],[14,37,67,82,90]],[82,168,[18,62,67,90],[14,37,68,81]],[90,168,[14,37,68,82],[18,62,67,81]],[71,296,[63,68,91],[15,38,51,82,84,87]],[87,296,[15,38,63,68,82],[51,71,84,91]],[45,224,[19,88,90],[16,59,67,69,76,81]],[69,224,[16,76,81],[19,45,59,67,88,90]],[76,224,[19,67,69,90],[16,45,59,81,88]],[81,224,[19,59,69,88],[16,45,67,76,90]],[88,224,[16,45,67,81],[19,59,69,76,90]],[90,224,[16,45,59,76],[19,67,69,81,88]],[17,52,[24,48,54,55,70,74,84,85,89],[53,73,88]],[53,52,[70,74,84,85,89],[17,24,48,54,55,73,88]],[73,52,[48,54,55,84,85,89],[17,24,53,70,74,88]],[85,52,[17,24,53,54,55,73,74,88],[48,70,84,89]],[88,52,[24,48,55,70,84,85,89],[17,53,54,73,74]],[53,112,[19,78,83,90],[17,42,61,69,73]],[69,112,[17,73,78],[19,42,53,61,83,90]],[83,112,[17,53,61],[19,42,69,73,78,90]],[90,112,[17,42,53,73],[19,61,69,78,83]],[79,56,[48,61,63,84,85,91],[18,33,62,70,78,90]],[85,56,[18,33,61,62,63,78,79,90],[48,70,84,91]],[91,56,[18,33,48,61,62,70,78,79,90],[63,84,85]],[69,176,[18,74,79],[19,43,54,62,83,88]],[79,176,[19,54,69,88],[18,43,62,74,83]],[83,176,[18,54,62],[19,43,69,74,79,88]],[88,176,[18,43,62,79],[19,54,69,74,83]],[20,30,[70],[]],[70,30,[20],[]],[21,45,[48,51],[]],[48,45,[21,51],[]],[51,45,[21,48],[]],[23,526,[72],[]],[72,526,[23],[]],[24,51,[33,42,43],[]],[33,51,[24,42,43],[]],[42,51,[24,33,43],[]],[43,51,[24,33,42],[]],[26,150,[74,75],[]],[74,150,[26,75],[]],[75,150,[26,74],[]],[28,165,[54,59],[]],[54,165,[28,59],[]],[59,165,[28,54],[]],[34,90,[78,80],[]],[78,90,[34,80],[]],[80,90,[34,78],[]],[36,105,[61,67],[]],[61,105,[36,67],[]],[67,105,[36,61],[]],[46,353,[60],[]],[60,353,[46],[]],[47,417,[68],[]],[68,417,[47],[]],[86,284,[49,84],[]],[55,305,[63],[]],[63,305,[55],[]],[85,556,[87],[]],[87,556,[85],[]],[89,816,[91],[]],[91,816,[89],[]]],\"edges\":[[34,[6,9,50,57,58,65,66,85,86,89,91]],[44,[7,10,32,41,52,58,66,72,86,87,89,91]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-28,-26],[-30,-2],[-30,-23],[-31,-1],[-31,-26],[-31,-28],[-32,-2],[-32,-23],[-32,-24],[-32,-26],[-32,-30],[-32,-31],[-33,-30],[-33,-32],[-36,-26],[-38,-28],[-38,-30],[-38,-36],[-39,-23],[-39,-28],[-39,-30],[-39,-38],[-40,-3],[-40,-31],[-40,-38],[-41,-21],[-41,-22],[-41,-23],[-41,-24],[-41,-36],[-41,-38],[-41,-39],[-41,-40],[-42,-4],[-42,-33],[-42,-39],[-42,-41],[-45,-26],[-45,-31],[-45,-36],[-45,-40],[-46,-28],[-46,-30],[-46,-31],[-46,-38],[-46,-39],[-46,-40],[-46,-45],[-51,-21],[-51,-22],[-51,-23],[-51,-24],[-53,-33],[-53,-51],[-54,-26],[-54,-28],[-54,-30],[-54,-38],[-54,-39],[-54,-46],[-57,-26],[-57,-45],[-57,-54],[-58,-21],[-58,-26],[-58,-49],[-58,-50],[-58,-51],[-58,-54],[-58,-57],[-59,-24],[-59,-33],[-59,-53],[-59,-58],[-63,-28],[-63,-30],[-63,-36],[-63,-38],[-63,-39],[-63,-46],[-63,-54],[-65,-36],[-65,-40],[-65,-45],[-65,-57],[-65,-63],[-66,-21],[-66,-36],[-66,-49],[-66,-51],[-66,-63],[-66,-65],[-67,-24],[-67,-42],[-67,-51],[-67,-53],[-67,-59],[-67,-66],[-70,-28],[-70,-30],[-70,-38],[-70,-39],[-70,-45],[-70,-46],[-70,-54],[-70,-57],[-70,-63],[-70,-65],[-72,-23],[-72,-30],[-72,-39],[-72,-50],[-72,-51],[-72,-53],[-73,-30],[-73,-33],[-73,-39],[-73,-42],[-73,-72],[-74,-26],[-74,-28],[-74,-36],[-74,-45],[-74,-54],[-77,-28],[-77,-31],[-77,-46],[-77,-57],[-77,-74],[-78,-22],[-78,-28],[-78,-30],[-78,-32],[-78,-71],[-78,-72],[-78,-74],[-78,-77],[-80,-26],[-80,-36],[-80,-38],[-80,-45],[-80,-63],[-80,-74],[-82,-38],[-82,-40],[-82,-46],[-82,-65],[-82,-77],[-82,-80],[-83,-22],[-83,-38],[-83,-39],[-83,-41],[-83,-72],[-83,-80],[-83,-82],[-84,-26],[-84,-36],[-84,-45],[-84,-46],[-84,-70],[-84,-74],[-84,-77],[-84,-80],[-84,-82],[-85,-59],[-85,-67],[-86,-22],[-86,-23],[-86,-51],[-86,-71],[-86,-72],[-89,-18],[-89,-31],[-89,-54],[-89,-57],[-89,-70],[-89,-74],[-89,-77],[-89,-84],[-90,-59],[-90,-67],[-91,-40],[-91,-63],[-91,-65],[-91,-70],[-91,-80],[-91,-82],[-91,-84],[-91,-89],[-1,2,21,22,23,24,25,27,29,30,33],[-26,2,22,23,24,29,30,33],[-28,2,21,23,24,27,33],[-31,2,21,22,23,24,25,30,33],[-33,1,21,22,25,26,27,28,29,31],[-26,5,37,40,46,47],[-28,5,35,40,45],[-32,5,35,37,40,43,45,46],[-40,1,26,28,32,43,47],[-45,1,28,32,37,47],[-46,1,26,32,35],[-31,6,54,58,61],[-32,6,54,57,58,60],[-54,1,31,32],[-57,1,28,32,61],[-58,1,28,31,32,60,61],[-31,13,74,78],[-32,13,74,76,77],[-74,1,31,32],[-77,1,26,32],[-78,1,26,31,76],[-32,4,39,41,42,48],[-33,4,39,41,47,48],[-41,2,30,32,33,47],[-42,2,30,32,47,48],[-8,2,23,30,32,50,52,56,61],[-23,8,56,59,61],[-32,8,50,52,53,56,59],[-53,2,30,32,56,61],[-59,2,23,30,32,52,61],[-32,14,72,73],[-33,14,72,78],[-72,2,32,33],[-78,2,23,33,73],[-4,3,21,22,24,34,35,36,37,38,40],[-38,4,21,23,24,35,42],[-39,3,21,24,35,36,40],[-40,4,21,22,23,24,34,39,42],[-3,5,27,29,31,44,45,46,48],[-31,3,36,38,41,44,48],[-36,5,29,31,46,48],[-41,5,27,29,31,44,45,46],[-45,3,29,38,41,48],[-46,3,27,36,41],[-40,9,63,66,69],[-41,9,63,65,66,68],[-65,3,38,41,69],[-66,3,38,40,41,68,69],[-40,15,80,83],[-41,15,80,81,82],[-82,3,36,41],[-83,3,36,40,81],[-11,4,23,39,41,50,52,64,69],[-41,11,50,52,53,64,67],[-53,4,39,41,64,69],[-67,4,23,39,41,52,69],[-41,16,72,73],[-72,4,41,42],[-83,4,23,42,73],[-31,12,65,68,70],[-40,12,57,60,70],[-46,12,57,65],[-57,5,40,46,68],[-65,5,31,46,60],[-70,5,31,40],[-31,17,81,82,84],[-40,17,76,77,84],[-45,17,77,82],[-82,5,31,45,76],[-26,12,62,65,70],[-45,6,54,58,62],[-54,12,35,45,65],[-58,12,35,43,45,62,65,70],[-26,18,89],[-57,18,74],[-58,18,74,76,89],[-74,6,57,58],[-89,6,26,58],[-7,8,24,33,53],[-33,7,51,58],[-51,8,33],[-58,8,24,33,53],[-58,10,66,67],[-59,10,66],[-66,7,58,59],[-67,7,58],[-7,86,87,90],[-51,90],[-58,86,87,90],[-59,86],[-8,11,42,67],[-33,11,67],[-42,8,59],[-59,11,42],[-67,8,33],[-8,73,87,88,90],[-33,87,88,90],[-53,90],[-59,73,88],[-88,8,33,59],[-90,8,33,53,73],[-67,9,21,34,35,36,49,62,63,65],[-36,12,55,57,70],[-63,12,27,45,57],[-66,12,27,44,45,55,57,70],[-70,9,27,36,66],[-36,19,91],[-65,19,80],[-66,19,80,81,91],[-91,9,36,66],[-42,10,51,66],[-51,11,42],[-66,11,24,42,53],[-10,86,87,92],[-51,92],[-66,86,87,92],[-67,86],[-92,10,51,66],[-11,73,87,88,92],[-42,87,88,92],[-53,92],[-67,73,88],[-92,11,42,53,73],[-57,20,81,84,91],[-65,20,76,84,89],[-89,12,45,65,81],[-91,12,45,57,76],[-13,14,22,25,29,30,71,72,75],[-28,14,71,72,75],[-30,13,71,74,75,77],[-72,13,25,28,29,74,75,77],[-74,14,22,29,30,72],[-77,14,22,25,30,71,72],[-28,17,79,82,84],[-46,13,74,78,79],[-74,17,37,46,47,82],[-78,17,37,43,46,79,82,84],[-82,13,28,43,47,74,78],[-84,13,28,37,47,78],[-18,13,28,60,61,77,78],[-28,18,89],[-77,18,54,61],[-78,18,54,60,89],[-89,13,28,61,78],[-16,14,30,47,48,78],[-39,14,78],[-78,16,39,48,83],[-83,14,30,47,78],[-72,56,61,90],[-78,52,56,85,88,90],[-88,14,30,56,61,78],[-15,16,22,34,37,39,71,72,79],[-38,16,71,72,79],[-39,15,71,79,80,82],[-72,15,34,37,38,79,80,82],[-80,16,22,37,39,72],[-82,16,22,34,39,71,72],[-46,15,75,80,83],[-80,17,29,46,48,77],[-83,17,29,44,46,75,77,84],[-84,15,29,38,48,83],[-19,15,38,68,69,82,83],[-38,19,91],[-82,19,63,69],[-83,19,63,68,91],[-91,15,38,69,83],[-72,64,69,92],[-88,16,39,64,69,83],[-46,20,89,91],[-70,17,77,82],[-77,20,68,70,91],[-82,20,60,70,89],[-89,17,46,68,82],[-91,17,46,60,77],[-18,25,49,55,56,71,75,85,86,90],[-54,71,75,85,86,90],[-74,49,55,56,85,86,90],[-86,18,25,54,55,56,74,75,89],[-89,25,49,56,71,85,86,90],[-54,20,79,84,91],[-70,18,74,79],[-84,18,54,62],[-91,18,43,54,74],[-80,49,62,64,85,86,92],[-86,19,34,62,63,64,79,80,91],[-92,19,34,49,62,63,71,79,80,91],[-70,19,75,80],[-80,20,55,70,89],[-84,19,55,63],[-89,19,44,63,80],[-21,71],[-71,21],[-22,49,52],[-49,22,52],[-52,22,49],[-24,73],[-73,24],[-25,34,43,44],[-34,25,43,44],[-43,25,34,44],[-44,25,34,43],[-27,75,76],[-75,27,76],[-76,27,75],[-29,55,60],[-55,29,60],[-60,29,55],[-35,79,81],[-79,35,81],[-81,35,79],[-37,62,68],[-62,37,68],[-68,37,62],[-47,61],[-61,47],[-48,69],[-69,48],[-87,50,85],[-56,64],[-64,56],[-86,88],[-88,86],[-90,92],[-92,90],[-1,93],[-2,94],[-3,95],[-4,96],[-5,97],[-6,98],[-7,99],[-8,100],[-9,101],[-10,102],[-11,103],[-12,104],[-13,105],[-14,106],[-15,107],[-16,108],[-17,109],[-18,110],[-19,111],[-20,112],[-94,113],[-93,113],[-93,-94,114],[-97,115],[-96,115],[-115,116],[-95,116],[-95,-115,117],[-116,118],[-117,119],[-113,118],[-113,-116,119],[-113,-117,120],[-114,119],[-114,-116,120],[-99,121],[-98,121],[-98,-99,122],[-102,123],[-101,123],[-101,-102,124],[-123,125],[-124,126],[-100,125],[-100,-123,126],[-125,127],[-126,128],[-121,127],[-121,-125,128],[-122,128],[-127,129],[-128,130],[-118,129],[-118,-127,130],[-118,-128,131],[-119,130],[-119,-127,131],[-120,131],[-120,-127,132],[-104,133],[-103,133],[-103,-104,134],[-107,135],[-106,135],[-135,136],[-105,136],[-105,-135,137],[-136,138],[-137,139],[-133,138],[-133,-136,139],[-133,-137,140],[-134,139],[-134,-136,140],[-109,141],[-108,141],[-108,-109,142],[-112,143],[-111,143],[-111,-112,144],[-143,145],[-144,146],[-110,145],[-110,-143,146],[-145,147],[-146,148],[-141,147],[-141,-145,148],[-141,-146,149],[-142,148],[-142,-145,149],[-147,150],[-148,151],[-149,152],[-138,150],[-138,-147,151],[-138,-148,152],[-138,-149,153],[-139,151],[-139,-147,152],[-139,-148,153],[-139,-149,154],[-140,-147,153],[-140,-148,154],[-154,155],[-129,-153,155],[-130,-152,155],[-131,-151,155],[-132,-150,155],[-155],[-156,51,58,59],[-58,156],[-59,156],[-157,66,67],[-66,157],[-67,157],[-158,23,33,42,53],[-33,158],[-42,158],[-53,158],[-159,28,30,32,78],[-28,159],[-30,159],[-32,159],[-78,159],[-160,39,72,83],[-72,160],[-83,160],[-161,31,57,77,89],[-31,161],[-57,161],[-77,161],[-89,161],[-162,36,38,40,41],[-38,162],[-40,162],[-41,162],[-163,46,54,63,70],[-46,163],[-54,163],[-63,163],[-70,163],[-164,26,45,74,80,84],[-45,164],[-74,164],[-80,164],[-165,65,82,91],[-65,165],[-82,165],[-91,165],[-166,156,157],[-167,156],[-167,157],[-156,-157,167],[-168,159,160],[-160,168],[-169,159],[-159,168],[-169,160],[-159,-160,169],[-170,158,168],[-171,158,169],[-172,158],[-171,168],[-158,-168,171],[-172,169],[-158,-169,172],[-173,166,172],[-174,166],[-173,167,171],[-174,167,172],[-175,167],[-173,170],[-174,171],[-167,-171,174],[-175,172],[-167,-172,175],[-176,161,162],[-177,161],[-161,176],[-177,162],[-161,-162,177],[-178,164,165],[-165,178],[-179,164],[-164,178],[-179,165],[-164,-165,179],[-180,163,178],[-181,163,179],[-179,181],[-182,163],[-181,178],[-163,-178,181],[-182,179],[-163,-179,182],[-183,176,182],[-184,176],[-183,177,181],[-184,177,182],[-176,-182,184],[-185,177],[-183,180],[-184,181],[-177,-181,184],[-185,182],[-177,-182,185],[-186,173],[-186,174,185],[-186,175,184],[-174,-185,187],[-186,183],[-175,-184,187],[186],[-187],[-50,188],[-86,188],[-90,188],[-85,189],[-88,189],[-92,189],[-22,190],[-87,190],[-49,191],[-73,191],[-25,192],[-27,192],[-35,192],[-193,34,75,79],[-34,193],[-75,193],[-79,193],[-194,43,76,81],[-43,194],[-76,194],[-81,194],[-195,29,37,44,47,48,52,56],[-29,195],[-37,195],[-44,195],[-47,195],[-48,195],[-52,195],[-56,195],[-196,55,61,62,64,69],[-55,196],[-61,196],[-62,196],[-64,196],[-69,196],[-197,60,68],[-60,197],[-68,197],[-189,198],[-188,198],[-192,199],[-191,199],[-199,200],[-190,200],[-200,201],[-198,201],[-198,-200,202],[-203,193,194],[-194,203],[-193,203],[-193,-194,204],[-205,196,197],[-197,205],[-196,205],[-196,-197,206],[-207,195,205],[-206,208],[-195,207],[-195,-205,208],[-209,203,207],[-207,209],[-208,210],[-203,209],[-203,-207,210],[-204,210],[-201,-210,211],[-202,-209,211],[-211],[-1,-10,-11,-16,-33,-41,-46,-58,-65,-78,-80,-86,-88,-89],[-1,-10,-11,-16,-33,-41,-45,-58,-63,-78,-82,-86,-88,-89],[-1,-10,-11,-16,-33,-41,-46,-58,-65,-78,-80,-85,-87,-89],[-1,-10,-11,-16,-33,-41,-45,-58,-63,-78,-82,-85,-87,-89],[-6,-7,-11,-19,-28,-33,-41,-45,-66,-72,-82,-89,-90,-92],[-6,-7,-11,-19,-31,-33,-41,-66,-70,-72,-74,-82,-90,-92],[-6,-7,-8,-18,-32,-40,-42,-66,-70,-72,-77,-80,-90,-92],[-7,-8,-12,-20,-32,-40,-42,-54,-66,-72,-77,-80,-90,-92],[-6,-7,-8,-18,-32,-38,-42,-45,-66,-72,-77,-90,-91,-92],[-1,-7,-11,-15,-33,-41,-45,-54,-66,-72,-77,-90,-91,-92],[-1,-2,-10,-16,-41,-45,-53,-58,-63,-78,-82,-89,-90,-92],[-1,-10,-11,-16,-33,-41,-45,-58,-63,-78,-82,-89,-90,-92],[-7,-14,-15,-16,-32,-41,-45,-53,-54,-66,-77,-90,-91,-92],[-1,-10,-11,-13,-33,-41,-45,-58,-63,-72,-82,-89,-90,-92],[-7,-8,-11,-15,-32,-41,-45,-54,-66,-72,-77,-90,-91,-92],[-1,-7,-11,-15,-33,-41,-46,-57,-66,-72,-74,-90,-91,-92],[-1,-2,-10,-16,-41,-46,-53,-58,-65,-78,-80,-89,-90,-92],[-1,-10,-11,-16,-33,-41,-46,-58,-65,-78,-80,-89,-90,-92],[-7,-14,-15,-16,-32,-41,-46,-53,-57,-66,-74,-90,-91,-92],[-1,-10,-11,-13,-33,-41,-46,-58,-65,-72,-80,-89,-90,-92],[-7,-8,-11,-15,-32,-41,-46,-57,-66,-72,-74,-90,-91,-92],[-5,-7,-8,-17,-32,-38,-42,-57,-66,-72,-74,-90,-91,-92],[-7,-16,-17,-20,-31,-33,-41,-54,-65,-67,-78,-80,-86,-88],[-7,-15,-16,-19,-31,-33,-41,-54,-65,-67,-78,-84,-86,-88],[-7,-15,-16,-19,-26,-33,-41,-46,-65,-67,-78,-86,-88,-89],[-1,-6,-7,-16,-33,-41,-46,-65,-67,-78,-80,-86,-88,-89],[-5,-7,-12,-16,-26,-33,-41,-63,-67,-78,-82,-86,-88,-89],[-1,-6,-7,-16,-33,-41,-45,-63,-67,-78,-82,-86,-88,-89],[-2,-10,-12,-17,-31,-36,-42,-54,-59,-78,-83,-86,-88,-91],[-1,-4,-7,-18,-33,-40,-57,-63,-67,-78,-83,-84,-86,-88],[-1,-2,-10,-18,-36,-42,-46,-57,-59,-78,-83,-86,-88,-91],[-1,-2,-10,-18,-40,-42,-57,-59,-63,-78,-83,-84,-86,-88],[-1,-4,-7,-18,-33,-36,-46,-57,-67,-78,-83,-86,-88,-91],[-2,-10,-12,-17,-26,-40,-42,-59,-63,-78,-83,-86,-88,-89],[-8,-13,-14,-18,-32,-36,-42,-46,-51,-57,-83,-90,-91,-92],[-1,-6,-11,-16,-33,-41,-46,-51,-65,-78,-80,-89,-90,-92],[-8,-14,-17,-20,-32,-40,-42,-51,-57,-63,-74,-83,-90,-92],[-8,-13,-14,-18,-32,-40,-42,-51,-57,-63,-83,-84,-90,-92],[-5,-8,-12,-14,-32,-36,-42,-51,-54,-77,-83,-90,-91,-92],[-1,-6,-11,-16,-33,-41,-45,-51,-63,-78,-82,-89,-90,-92],[-2,-8,-12,-17,-31,-36,-42,-51,-54,-78,-83,-90,-91,-92],[-1,-4,-11,-18,-33,-40,-51,-57,-63,-78,-83,-84,-90,-92],[-1,-2,-8,-18,-36,-42,-46,-51,-57,-78,-83,-90,-91,-92],[-1,-2,-8,-18,-40,-42,-51,-57,-63,-78,-83,-84,-90,-92],[-1,-4,-11,-18,-33,-36,-46,-51,-57,-78,-83,-90,-91,-92],[-2,-8,-12,-17,-26,-40,-42,-51,-63,-78,-83,-89,-90,-92],[-8,-14,-16,-18,-32,-38,-42,-45,-58,-66,-77,-86,-88,-91],[-8,-14,-16,-18,-32,-40,-42,-58,-66,-70,-77,-80,-86,-88],[-1,-11,-16,-19,-33,-41,-45,-58,-66,-78,-82,-86,-88,-89],[-1,-3,-8,-18,-30,-42,-45,-58,-66,-77,-83,-86,-88,-91],[-1,-11,-12,-16,-33,-41,-46,-58,-66,-78,-80,-86,-88,-89],[-1,-11,-12,-17,-33,-39,-40,-58,-66,-78,-80,-86,-88,-89],[-8,-14,-18,-19,-32,-40,-42,-58,-66,-70,-77,-83,-86,-88],[-8,-14,-17,-19,-32,-40,-42,-58,-66,-70,-74,-83,-86,-88],[-8,-14,-16,-18,-32,-38,-42,-45,-58,-66,-77,-85,-87,-91],[-8,-14,-16,-18,-32,-40,-42,-58,-66,-70,-77,-80,-85,-87],[-1,-11,-16,-19,-33,-41,-45,-58,-66,-78,-82,-85,-87,-89],[-1,-3,-8,-18,-30,-42,-45,-58,-66,-77,-83,-85,-87,-91],[-1,-11,-12,-16,-33,-41,-46,-58,-66,-78,-80,-85,-87,-89],[-1,-11,-12,-17,-33,-39,-40,-58,-66,-78,-80,-85,-87,-89],[-8,-14,-18,-19,-32,-40,-42,-58,-66,-70,-77,-83,-85,-87],[-8,-14,-17,-19,-32,-40,-42,-58,-66,-70,-74,-83,-85,-87],[-8,-18,-19,-20,-32,-38,-42,-45,-58,-66,-72,-77,-90,-92],[-8,-15,-18,-19,-32,-40,-42,-58,-66,-70,-72,-77,-90,-92],[-2,-16,-18,-19,-31,-41,-53,-58,-66,-70,-78,-82,-90,-92],[-8,-14,-18,-19,-32,-40,-42,-58,-66,-70,-77,-83,-90,-92],[-12,-14,-18,-20,-32,-39,-40,-53,-58,-66,-77,-80,-90,-92],[-8,-12,-18,-20,-32,-40,-42,-58,-66,-72,-77,-80,-90,-92],[-2,-16,-17,-18,-31,-41,-53,-58,-66,-70,-78,-80,-90,-92],[-8,-14,-17,-19,-32,-40,-42,-58,-66,-70,-74,-83,-90,-92],[-5,-14,-16,-18,-32,-41,-53,-58,-66,-70,-77,-80,-90,-92],[-2,-14,-16,-19,-31,-41,-53,-58,-66,-70,-74,-82,-90,-92],[-8,-14,-16,-18,-32,-40,-42,-58,-66,-70,-77,-80,-90,-92],[-8,-13,-17,-18,-32,-40,-42,-58,-66,-70,-72,-80,-90,-92],[-8,-15,-17,-19,-32,-40,-42,-58,-66,-70,-72,-74,-90,-92],[-1,-2,-8,-18,-40,-42,-58,-66,-70,-72,-77,-80,-90,-92],[-1,-5,-11,-18,-33,-41,-58,-66,-70,-72,-77,-80,-90,-92],[-1,-4,-11,-18,-33,-40,-58,-66,-70,-72,-77,-80,-90,-92],[-1,-5,-11,-19,-33,-41,-58,-66,-70,-72,-74,-82,-90,-92],[-5,-8,-11,-18,-32,-41,-58,-66,-70,-72,-77,-80,-90,-92],[-2,-8,-11,-19,-31,-41,-58,-66,-70,-72,-74,-82,-90,-92],[-5,-8,-12,-18,-32,-38,-42,-58,-66,-72,-77,-90,-91,-92],[-8,-13,-17,-19,-32,-38,-42,-45,-58,-66,-72,-89,-90,-92],[-8,-13,-17,-18,-32,-38,-42,-45,-58,-66,-72,-90,-91,-92],[-1,-2,-3,-19,-39,-45,-53,-58,-66,-78,-82,-89,-90,-92],[-1,-3,-8,-18,-30,-42,-45,-58,-66,-77,-83,-90,-91,-92],[-1,-15,-16,-18,-30,-41,-45,-53,-58,-66,-77,-90,-91,-92],[-1,-2,-8,-18,-38,-42,-45,-58,-66,-72,-77,-90,-91,-92],[-1,-11,-15,-18,-33,-41,-45,-58,-66,-72,-77,-90,-91,-92],[-1,-4,-11,-18,-33,-38,-45,-58,-66,-72,-77,-90,-91,-92],[-1,-11,-16,-19,-33,-41,-45,-58,-66,-78,-82,-89,-90,-92],[-8,-14,-16,-18,-32,-38,-42,-45,-58,-66,-77,-90,-91,-92],[-1,-2,-16,-19,-41,-45,-53,-58,-66,-78,-82,-89,-90,-92],[-1,-13,-16,-19,-30,-41,-45,-53,-58,-66,-82,-89,-90,-92],[-2,-14,-16,-19,-28,-41,-45,-53,-58,-66,-82,-89,-90,-92],[-13,-14,-16,-19,-32,-41,-45,-53,-58,-66,-82,-89,-90,-92],[-1,-11,-13,-19,-33,-41,-45,-58,-66,-72,-82,-89,-90,-92],[-8,-11,-13,-19,-32,-41,-45,-58,-66,-72,-82,-89,-90,-92],[-2,-8,-11,-19,-28,-41,-45,-58,-66,-72,-82,-89,-90,-92],[-5,-8,-12,-17,-32,-38,-42,-58,-66,-72,-74,-90,-91,-92],[-1,-2,-12,-17,-39,-40,-53,-58,-66,-78,-80,-89,-90,-92],[-1,-11,-12,-17,-33,-39,-40,-58,-66,-78,-80,-89,-90,-92],[-12,-13,-14,-17,-32,-39,-40,-53,-58,-66,-80,-89,-90,-92],[-2,-8,-12,-17,-31,-38,-42,-58,-66,-72,-74,-90,-91,-92],[-8,-12,-13,-17,-32,-40,-42,-58,-66,-72,-80,-89,-90,-92],[-2,-8,-12,-17,-28,-40,-42,-58,-66,-72,-80,-89,-90,-92],[-1,-2,-12,-16,-41,-46,-53,-58,-66,-78,-80,-89,-90,-92],[-1,-11,-12,-16,-33,-41,-46,-58,-66,-78,-80,-89,-90,-92],[-12,-13,-14,-16,-32,-41,-46,-53,-58,-66,-80,-89,-90,-92],[-1,-11,-12,-13,-33,-41,-46,-58,-66,-72,-80,-89,-90,-92],[-1,-11,-12,-15,-33,-41,-46,-58,-66,-72,-74,-90,-91,-92],[-8,-11,-12,-13,-32,-41,-46,-58,-66,-72,-80,-89,-90,-92],[-8,-13,-14,-16,-32,-41,-46,-58,-65,-67,-80,-86,-88,-89],[-8,-13,-14,-16,-32,-41,-45,-58,-63,-67,-82,-86,-88,-89],[-1,-2,-8,-16,-41,-46,-58,-65,-67,-78,-80,-86,-88,-89],[-1,-2,-8,-16,-41,-45,-58,-63,-67,-78,-82,-86,-88,-89],[-5,-14,-16,-17,-28,-33,-41,-58,-65,-67,-80,-86,-88,-89],[-1,-13,-14,-16,-33,-41,-46,-58,-65,-67,-80,-86,-88,-89],[-6,-14,-16,-18,-32,-38,-42,-45,-59,-66,-77,-86,-88,-91],[-1,-13,-14,-16,-33,-41,-45,-58,-63,-67,-82,-86,-88,-89],[-12,-14,-16,-20,-31,-33,-41,-58,-63,-67,-74,-82,-86,-88],[-6,-14,-16,-18,-32,-40,-42,-59,-66,-70,-77,-80,-86,-88],[-1,-16,-18,-20,-33,-41,-46,-58,-65,-67,-78,-80,-86,-88],[-1,-16,-18,-20,-33,-41,-45,-58,-63,-67,-78,-82,-86,-88],[-1,-4,-12,-18,-33,-36,-46,-58,-67,-78,-83,-86,-88,-91],[-1,-4,-12,-18,-33,-40,-58,-63,-67,-78,-83,-84,-86,-88],[-1,-9,-16,-19,-33,-41,-45,-58,-67,-78,-82,-86,-88,-89],[-1,-3,-6,-18,-30,-42,-45,-59,-66,-77,-83,-86,-88,-91],[-1,-4,-12,-19,-33,-36,-46,-58,-67,-78,-83,-86,-88,-89],[-1,-5,-12,-19,-33,-36,-39,-58,-67,-78,-82,-86,-88,-89],[-1,-15,-16,-19,-33,-41,-46,-58,-65,-67,-78,-86,-88,-89],[-1,-2,-3,-18,-42,-46,-57,-59,-66,-78,-83,-86,-88,-91],[-1,-4,-12,-17,-33,-40,-58,-63,-67,-78,-83,-86,-88,-89],[-1,-5,-12,-16,-33,-41,-58,-63,-67,-78,-82,-86,-88,-89],[-1,-15,-16,-17,-33,-41,-45,-58,-63,-67,-78,-86,-88,-89],[-1,-2,-3,-17,-42,-45,-54,-59,-66,-78,-83,-86,-88,-91],[-1,-2,-3,-14,-42,-45,-54,-59,-66,-77,-83,-86,-88,-91],[-1,-9,-12,-16,-33,-41,-46,-58,-67,-78,-80,-86,-88,-89],[-1,-9,-12,-17,-33,-39,-40,-58,-67,-78,-80,-86,-88,-89],[-1,-5,-16,-17,-33,-41,-58,-65,-67,-78,-80,-86,-88,-89],[-1,-2,-3,-14,-42,-46,-57,-59,-66,-74,-83,-86,-88,-91],[-1,-3,-5,-17,-30,-42,-57,-59,-66,-74,-83,-86,-88,-91],[-2,-12,-17,-19,-26,-40,-42,-59,-66,-78,-83,-86,-88,-89],[-12,-18,-19,-20,-26,-30,-40,-42,-59,-66,-77,-83,-86,-88],[-12,-13,-17,-19,-26,-30,-40,-42,-59,-66,-83,-86,-88,-89],[-12,-14,-19,-20,-32,-40,-42,-54,-59,-66,-77,-83,-86,-88],[-12,-13,-14,-19,-32,-40,-42,-54,-59,-66,-83,-84,-86,-88],[-1,-2,-12,-19,-40,-42,-54,-59,-66,-78,-83,-84,-86,-88],[-1,-2,-18,-19,-40,-42,-57,-59,-66,-78,-83,-84,-86,-88],[-1,-13,-18,-19,-30,-40,-42,-57,-59,-66,-83,-84,-86,-88],[-2,-14,-18,-19,-28,-40,-42,-57,-59,-66,-83,-84,-86,-88],[-13,-14,-18,-19,-32,-40,-42,-57,-59,-66,-83,-84,-86,-88],[-14,-17,-19,-20,-32,-40,-42,-57,-59,-66,-74,-83,-86,-88],[-1,-17,-19,-20,-30,-40,-42,-57,-59,-66,-74,-83,-86,-88],[-6,-14,-18,-19,-32,-40,-42,-59,-66,-70,-77,-83,-86,-88],[-6,-14,-17,-19,-32,-40,-42,-59,-66,-70,-74,-83,-86,-88],[-2,-17,-18,-19,-26,-40,-42,-59,-66,-70,-78,-83,-86,-88],[-2,-14,-18,-19,-26,-40,-42,-59,-66,-70,-77,-83,-86,-88],[-3,-7,-8,-14,-32,-42,-46,-57,-66,-74,-83,-86,-88,-91],[-3,-7,-8,-14,-32,-42,-45,-54,-66,-77,-83,-86,-88,-91],[-3,-7,-8,-14,-32,-42,-46,-57,-66,-74,-83,-85,-87,-91],[-3,-7,-8,-14,-32,-42,-45,-54,-66,-77,-83,-85,-87,-91],[-8,-9,-10,-18,-32,-38,-42,-45,-58,-72,-77,-90,-91,-92],[-8,-9,-10,-18,-32,-40,-42,-58,-70,-72,-77,-80,-90,-92],[-9,-10,-11,-19,-31,-33,-41,-58,-70,-72,-74,-82,-90,-92],[-10,-11,-12,-20,-31,-33,-41,-58,-63,-72,-74,-82,-90,-92],[-9,-10,-11,-19,-28,-33,-41,-45,-58,-72,-82,-89,-90,-92],[-3,-8,-10,-13,-32,-42,-45,-58,-63,-72,-82,-89,-90,-92],[-3,-4,-7,-14,-32,-45,-53,-54,-66,-77,-83,-90,-91,-92],[-3,-7,-8,-14,-32,-42,-45,-54,-66,-77,-83,-90,-91,-92],[-10,-13,-14,-16,-32,-41,-45,-53,-58,-63,-82,-89,-90,-92],[-3,-7,-8,-15,-32,-42,-45,-54,-66,-72,-77,-90,-91,-92],[-8,-10,-11,-13,-32,-41,-45,-58,-63,-72,-82,-89,-90,-92],[-3,-8,-10,-13,-32,-42,-46,-58,-65,-72,-80,-89,-90,-92],[-3,-4,-7,-14,-32,-46,-53,-57,-66,-74,-83,-90,-91,-92],[-3,-7,-8,-14,-32,-42,-46,-57,-66,-74,-83,-90,-91,-92],[-10,-13,-14,-16,-32,-41,-46,-53,-58,-65,-80,-89,-90,-92],[-3,-7,-8,-15,-32,-42,-46,-57,-66,-72,-74,-90,-91,-92],[-8,-10,-11,-13,-32,-41,-46,-58,-65,-72,-80,-89,-90,-92],[-5,-10,-11,-17,-28,-33,-41,-58,-65,-72,-80,-89,-90,-92],[-10,-14,-17,-20,-32,-40,-42,-57,-59,-63,-74,-83,-86,-88],[-10,-13,-14,-18,-32,-40,-42,-57,-59,-63,-83,-84,-86,-88],[-10,-13,-14,-18,-32,-36,-42,-46,-57,-59,-83,-86,-88,-91],[-3,-9,-10,-14,-32,-42,-46,-57,-59,-74,-83,-86,-88,-91],[-5,-10,-12,-14,-32,-36,-42,-54,-59,-77,-83,-86,-88,-91],[-3,-9,-10,-14,-32,-42,-45,-54,-59,-77,-83,-86,-88,-91],[-4,-7,-12,-17,-26,-33,-40,-63,-67,-78,-83,-86,-88,-89],[-2,-3,-10,-19,-31,-42,-54,-59,-65,-78,-83,-84,-86,-88],[-3,-4,-7,-19,-26,-33,-46,-65,-67,-78,-83,-86,-88,-89],[-3,-4,-7,-19,-31,-33,-54,-65,-67,-78,-83,-84,-86,-88],[-2,-3,-10,-19,-26,-42,-46,-59,-65,-78,-83,-86,-88,-89],[-4,-7,-12,-17,-31,-33,-36,-54,-67,-78,-83,-86,-88,-91],[-11,-15,-16,-19,-26,-33,-41,-46,-51,-65,-78,-89,-90,-92],[-3,-8,-9,-14,-32,-42,-46,-51,-57,-74,-83,-90,-91,-92],[-11,-16,-17,-20,-31,-33,-41,-51,-54,-65,-78,-80,-90,-92],[-11,-15,-16,-19,-31,-33,-41,-51,-54,-65,-78,-84,-90,-92],[-5,-11,-12,-16,-26,-33,-41,-51,-63,-78,-82,-89,-90,-92],[-3,-8,-9,-14,-32,-42,-45,-51,-54,-77,-83,-90,-91,-92],[-4,-11,-12,-17,-26,-33,-40,-51,-63,-78,-83,-89,-90,-92],[-2,-3,-8,-19,-31,-42,-51,-54,-65,-78,-83,-84,-90,-92],[-3,-4,-11,-19,-26,-33,-46,-51,-65,-78,-83,-89,-90,-92],[-3,-4,-11,-19,-31,-33,-51,-54,-65,-78,-83,-84,-90,-92],[-2,-3,-8,-19,-26,-42,-46,-51,-65,-78,-83,-89,-90,-92],[-4,-11,-12,-17,-31,-33,-36,-51,-54,-78,-83,-90,-91,-92],[-11,-14,-16,-19,-28,-33,-41,-45,-58,-66,-82,-86,-88,-89],[-11,-14,-16,-19,-31,-33,-41,-58,-66,-70,-74,-82,-86,-88],[-3,-8,-14,-18,-32,-42,-45,-58,-66,-77,-83,-86,-88,-91],[-1,-3,-11,-19,-33,-39,-45,-58,-66,-78,-82,-86,-88,-89],[-3,-8,-12,-14,-32,-42,-46,-58,-66,-74,-83,-86,-88,-91],[-3,-8,-12,-17,-30,-31,-42,-58,-66,-74,-83,-86,-88,-91],[-11,-16,-18,-19,-31,-33,-41,-58,-66,-70,-78,-82,-86,-88],[-11,-16,-17,-18,-31,-33,-41,-58,-66,-70,-78,-80,-86,-88],[-11,-14,-16,-19,-28,-33,-41,-45,-58,-66,-82,-85,-87,-89],[-11,-14,-16,-19,-31,-33,-41,-58,-66,-70,-74,-82,-85,-87],[-3,-8,-14,-18,-32,-42,-45,-58,-66,-77,-83,-85,-87,-91],[-1,-3,-11,-19,-33,-39,-45,-58,-66,-78,-82,-85,-87,-89],[-3,-8,-12,-14,-32,-42,-46,-58,-66,-74,-83,-85,-87,-91],[-3,-8,-12,-17,-30,-31,-42,-58,-66,-74,-83,-85,-87,-91],[-11,-16,-18,-19,-31,-33,-41,-58,-66,-70,-78,-82,-85,-87],[-11,-16,-17,-18,-31,-33,-41,-58,-66,-70,-78,-80,-85,-87],[-11,-18,-19,-20,-28,-33,-41,-45,-58,-66,-72,-82,-90,-92],[-11,-13,-18,-19,-31,-33,-41,-58,-66,-70,-72,-82,-90,-92],[-4,-14,-18,-19,-32,-40,-53,-58,-66,-70,-77,-83,-90,-92],[-11,-16,-18,-19,-31,-33,-41,-58,-66,-70,-78,-82,-90,-92],[-12,-16,-19,-20,-30,-31,-41,-53,-58,-66,-74,-82,-90,-92],[-11,-12,-19,-20,-31,-33,-41,-58,-66,-72,-74,-82,-90,-92],[-4,-14,-17,-19,-32,-40,-53,-58,-66,-70,-74,-83,-90,-92],[-11,-16,-17,-18,-31,-33,-41,-58,-66,-70,-78,-80,-90,-92],[-5,-14,-16,-19,-32,-41,-53,-58,-66,-70,-74,-82,-90,-92],[-4,-14,-16,-18,-32,-40,-53,-58,-66,-70,-77,-80,-90,-92],[-11,-14,-16,-19,-31,-33,-41,-58,-66,-70,-74,-82,-90,-92],[-11,-15,-17,-19,-31,-33,-41,-58,-66,-70,-72,-74,-90,-92],[-11,-13,-17,-18,-31,-33,-41,-58,-66,-70,-72,-80,-90,-92],[-3,-4,-11,-19,-31,-33,-58,-66,-70,-72,-74,-82,-90,-92],[-3,-5,-8,-19,-32,-42,-58,-66,-70,-72,-74,-82,-90,-92],[-2,-3,-8,-19,-31,-42,-58,-66,-70,-72,-74,-82,-90,-92],[-3,-5,-8,-18,-32,-42,-58,-66,-70,-72,-77,-80,-90,-92],[-5,-8,-11,-19,-32,-41,-58,-66,-70,-72,-74,-82,-90,-92],[-4,-8,-11,-18,-32,-40,-58,-66,-70,-72,-77,-80,-90,-92],[-5,-11,-12,-19,-28,-33,-41,-58,-66,-72,-82,-89,-90,-92],[-11,-15,-17,-18,-28,-33,-41,-45,-58,-66,-72,-90,-91,-92],[-11,-15,-17,-19,-28,-33,-41,-45,-58,-66,-72,-89,-90,-92],[-1,-3,-4,-18,-30,-45,-53,-58,-66,-77,-83,-90,-91,-92],[-1,-3,-11,-19,-33,-39,-45,-58,-66,-78,-82,-89,-90,-92],[-3,-13,-14,-19,-32,-39,-45,-53,-58,-66,-82,-89,-90,-92],[-3,-4,-11,-19,-28,-33,-45,-58,-66,-72,-82,-89,-90,-92],[-3,-8,-13,-19,-32,-42,-45,-58,-66,-72,-82,-89,-90,-92],[-2,-3,-8,-19,-28,-42,-45,-58,-66,-72,-82,-89,-90,-92],[-3,-8,-14,-18,-32,-42,-45,-58,-66,-77,-83,-90,-91,-92],[-11,-14,-16,-19,-28,-33,-41,-45,-58,-66,-82,-89,-90,-92],[-3,-4,-14,-18,-32,-45,-53,-58,-66,-77,-83,-90,-91,-92],[-3,-14,-15,-18,-32,-39,-45,-53,-58,-66,-77,-90,-91,-92],[-4,-14,-16,-18,-32,-38,-45,-53,-58,-66,-77,-90,-91,-92],[-14,-15,-16,-18,-32,-41,-45,-53,-58,-66,-77,-90,-91,-92],[-3,-8,-15,-18,-32,-42,-45,-58,-66,-72,-77,-90,-91,-92],[-8,-11,-15,-18,-32,-41,-45,-58,-66,-72,-77,-90,-91,-92],[-4,-8,-11,-18,-32,-38,-45,-58,-66,-72,-77,-90,-91,-92],[-5,-11,-12,-17,-28,-33,-41,-58,-66,-72,-80,-89,-90,-92],[-3,-4,-12,-17,-30,-31,-53,-58,-66,-74,-83,-90,-91,-92],[-3,-8,-12,-17,-30,-31,-42,-58,-66,-74,-83,-90,-91,-92],[-12,-15,-16,-17,-30,-31,-41,-53,-58,-66,-74,-90,-91,-92],[-4,-11,-12,-17,-28,-33,-40,-58,-66,-72,-80,-89,-90,-92],[-11,-12,-15,-17,-31,-33,-41,-58,-66,-72,-74,-90,-91,-92],[-4,-11,-12,-17,-31,-33,-38,-58,-66,-72,-74,-90,-91,-92],[-3,-4,-12,-14,-32,-46,-53,-58,-66,-74,-83,-90,-91,-92],[-3,-8,-12,-14,-32,-42,-46,-58,-66,-74,-83,-90,-91,-92],[-12,-14,-15,-16,-32,-41,-46,-53,-58,-66,-74,-90,-91,-92],[-3,-8,-12,-15,-32,-42,-46,-58,-66,-72,-74,-90,-91,-92],[-3,-8,-12,-13,-32,-42,-46,-58,-66,-72,-80,-89,-90,-92],[-8,-11,-12,-15,-32,-41,-46,-58,-66,-72,-74,-90,-91,-92],[-11,-14,-15,-16,-32,-41,-46,-57,-59,-66,-74,-86,-88,-91],[-11,-14,-15,-16,-32,-41,-45,-54,-59,-66,-77,-86,-88,-91],[-3,-4,-11,-14,-32,-46,-57,-59,-66,-74,-83,-86,-88,-91],[-3,-4,-11,-14,-32,-45,-54,-59,-66,-77,-83,-86,-88,-91],[-5,-14,-16,-17,-32,-38,-42,-57,-59,-66,-74,-86,-88,-91],[-3,-14,-15,-16,-32,-42,-46,-57,-59,-66,-74,-86,-88,-91],[-9,-14,-16,-19,-28,-33,-41,-45,-58,-67,-82,-86,-88,-89],[-3,-14,-15,-16,-32,-42,-45,-54,-59,-66,-77,-86,-88,-91],[-12,-14,-16,-20,-32,-40,-42,-54,-59,-66,-77,-80,-86,-88],[-9,-14,-16,-19,-31,-33,-41,-58,-67,-70,-74,-82,-86,-88],[-3,-14,-19,-20,-32,-42,-46,-57,-59,-66,-74,-83,-86,-88],[-3,-14,-19,-20,-32,-42,-45,-54,-59,-66,-77,-83,-86,-88],[-2,-3,-12,-19,-26,-42,-46,-59,-66,-78,-83,-86,-88,-89],[-2,-3,-12,-19,-31,-42,-54,-59,-66,-78,-83,-84,-86,-88],[-3,-6,-14,-18,-32,-42,-45,-59,-66,-77,-83,-86,-88,-91],[-1,-3,-9,-19,-33,-39,-45,-58,-67,-78,-82,-86,-88,-89],[-2,-3,-12,-18,-26,-42,-46,-59,-66,-78,-83,-86,-88,-91],[-3,-5,-12,-18,-26,-30,-42,-59,-66,-77,-83,-86,-88,-91],[-3,-13,-14,-18,-32,-42,-46,-57,-59,-66,-83,-86,-88,-91],[-1,-3,-4,-19,-33,-46,-58,-65,-67,-78,-83,-86,-88,-89],[-2,-3,-12,-17,-31,-42,-54,-59,-66,-78,-83,-86,-88,-91],[-3,-5,-12,-14,-32,-42,-54,-59,-66,-77,-83,-86,-88,-91],[-3,-13,-14,-17,-32,-42,-45,-54,-59,-66,-83,-86,-88,-91],[-1,-3,-4,-17,-33,-45,-58,-63,-67,-78,-83,-86,-88,-89],[-1,-3,-4,-16,-33,-45,-58,-63,-67,-78,-82,-86,-88,-89],[-3,-6,-12,-14,-32,-42,-46,-59,-66,-74,-83,-86,-88,-91],[-3,-6,-12,-17,-30,-31,-42,-59,-66,-74,-83,-86,-88,-91],[-3,-5,-14,-17,-32,-42,-57,-59,-66,-74,-83,-86,-88,-91],[-1,-3,-4,-16,-33,-46,-58,-65,-67,-78,-80,-86,-88,-89],[-1,-3,-5,-17,-33,-39,-58,-65,-67,-78,-80,-86,-88,-89],[-4,-12,-17,-18,-31,-33,-36,-58,-67,-78,-83,-86,-88,-91],[-12,-18,-19,-20,-31,-33,-36,-39,-58,-67,-78,-82,-86,-88],[-12,-15,-17,-18,-31,-33,-36,-39,-58,-67,-78,-86,-88,-91],[-12,-16,-18,-20,-31,-33,-41,-58,-63,-67,-78,-82,-86,-88],[-12,-15,-16,-18,-31,-33,-41,-58,-63,-67,-78,-84,-86,-88],[-3,-4,-12,-18,-31,-33,-58,-63,-67,-78,-83,-84,-86,-88],[-3,-4,-18,-19,-31,-33,-58,-65,-67,-78,-83,-84,-86,-88],[-3,-15,-18,-19,-31,-33,-39,-58,-65,-67,-78,-84,-86,-88],[-4,-16,-18,-19,-31,-33,-38,-58,-65,-67,-78,-84,-86,-88],[-15,-16,-18,-19,-31,-33,-41,-58,-65,-67,-78,-84,-86,-88],[-16,-17,-18,-20,-31,-33,-41,-58,-65,-67,-78,-80,-86,-88],[-3,-17,-18,-20,-31,-33,-39,-58,-65,-67,-78,-80,-86,-88],[-9,-16,-18,-19,-31,-33,-41,-58,-67,-70,-78,-82,-86,-88],[-9,-16,-17,-18,-31,-33,-41,-58,-67,-70,-78,-80,-86,-88],[-4,-17,-18,-19,-31,-33,-36,-58,-67,-70,-78,-83,-86,-88],[-4,-16,-18,-19,-31,-33,-36,-58,-67,-70,-78,-82,-86,-88],[7,10,51,58,59,66,67,86,87,90,92],[8,11,33,42,53,59,67,73,87,88,90,92]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":1,\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":3,\"kind\":1},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":27,\"b\":25},{\"tag\":\"incompatible\",\"a\":29,\"b\":1},{\"tag\":\"incompatible\",\"a\":29,\"b\":22},{\"tag\":\"incompatible\",\"a\":30,\"b\":0},{\"tag\":\"incompatible\",\"a\":30,\"b\":25},{\"tag\":\"incompatible\",\"a\":30,\"b\":27},{\"tag\":\"incompatible\",\"a\":31,\"b\":1},{\"tag\":\"incompatible\",\"a\":31,\"b\":22},{\"tag\":\"incompatible\",\"a\":31,\"b\":23},{\"tag\":\"incompatible\",\"a\":31,\"b\":25},{\"tag\":\"incompatible\",\"a\":31,\"b\":29},{\"tag\":\"incompatible\",\"a\":31,\"b\":30},{\"tag\":\"incompatible\",\"a\":32,\"b\":29},{\"tag\":\"incompatible\",\"a\":32,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":25},{\"tag\":\"incompatible\",\"a\":37,\"b\":27},{\"tag\":\"incompatible\",\"a\":37,\"b\":29},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":22},{\"tag\":\"incompatible\",\"a\":38,\"b\":27},{\"tag\":\"incompatible\",\"a\":38,\"b\":29},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":2},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":20},{\"tag\":\"incompatible\",\"a\":40,\"b\":21},{\"tag\":\"incompatible\",\"a\":40,\"b\":22},{\"tag\":\"incompatible\",\"a\":40,\"b\":23},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":3},{\"tag\":\"incompatible\",\"a\":41,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":25},{\"tag\":\"incompatible\",\"a\":44,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":27},{\"tag\":\"incompatible\",\"a\":45,\"b\":29},{\"tag\":\"incompatible\",\"a\":45,\"b\":30},{\"tag\":\"incompatible\",\"a\":45,\"b\":37},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":20},{\"tag\":\"incompatible\",\"a\":50,\"b\":21},{\"tag\":\"incompatible\",\"a\":50,\"b\":22},{\"tag\":\"incompatible\",\"a\":50,\"b\":23},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":25},{\"tag\":\"incompatible\",\"a\":53,\"b\":27},{\"tag\":\"incompatible\",\"a\":53,\"b\":29},{\"tag\":\"incompatible\",\"a\":53,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":38},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":56,\"b\":25},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":20},{\"tag\":\"incompatible\",\"a\":57,\"b\":25},{\"tag\":\"incompatible\",\"a\":57,\"b\":48},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":23},{\"tag\":\"incompatible\",\"a\":58,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":52},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":27},{\"tag\":\"incompatible\",\"a\":62,\"b\":29},{\"tag\":\"incompatible\",\"a\":62,\"b\":35},{\"tag\":\"incompatible\",\"a\":62,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":45},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":64,\"b\":35},{\"tag\":\"incompatible\",\"a\":64,\"b\":39},{\"tag\":\"incompatible\",\"a\":64,\"b\":44},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":20},{\"tag\":\"incompatible\",\"a\":65,\"b\":35},{\"tag\":\"incompatible\",\"a\":65,\"b\":48},{\"tag\":\"incompatible\",\"a\":65,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":23},{\"tag\":\"incompatible\",\"a\":66,\"b\":41},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":66,\"b\":52},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":27},{\"tag\":\"incompatible\",\"a\":69,\"b\":29},{\"tag\":\"incompatible\",\"a\":69,\"b\":37},{\"tag\":\"incompatible\",\"a\":69,\"b\":38},{\"tag\":\"incompatible\",\"a\":69,\"b\":44},{\"tag\":\"incompatible\",\"a\":69,\"b\":45},{\"tag\":\"incompatible\",\"a\":69,\"b\":53},{\"tag\":\"incompatible\",\"a\":69,\"b\":56},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":71,\"b\":22},{\"tag\":\"incompatible\",\"a\":71,\"b\":29},{\"tag\":\"incompatible\",\"a\":71,\"b\":38},{\"tag\":\"incompatible\",\"a\":71,\"b\":49},{\"tag\":\"incompatible\",\"a\":71,\"b\":50},{\"tag\":\"incompatible\",\"a\":71,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":29},{\"tag\":\"incompatible\",\"a\":72,\"b\":32},{\"tag\":\"incompatible\",\"a\":72,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":41},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":25},{\"tag\":\"incompatible\",\"a\":73,\"b\":27},{\"tag\":\"incompatible\",\"a\":73,\"b\":35},{\"tag\":\"incompatible\",\"a\":73,\"b\":44},{\"tag\":\"incompatible\",\"a\":73,\"b\":53},{\"tag\":\"incompatible\",\"a\":76,\"b\":27},{\"tag\":\"incompatible\",\"a\":76,\"b\":30},{\"tag\":\"incompatible\",\"a\":76,\"b\":45},{\"tag\":\"incompatible\",\"a\":76,\"b\":56},{\"tag\":\"incompatible\",\"a\":76,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":21},{\"tag\":\"incompatible\",\"a\":77,\"b\":27},{\"tag\":\"incompatible\",\"a\":77,\"b\":29},{\"tag\":\"incompatible\",\"a\":77,\"b\":31},{\"tag\":\"incompatible\",\"a\":77,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":25},{\"tag\":\"incompatible\",\"a\":79,\"b\":35},{\"tag\":\"incompatible\",\"a\":79,\"b\":37},{\"tag\":\"incompatible\",\"a\":79,\"b\":44},{\"tag\":\"incompatible\",\"a\":79,\"b\":62},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":81,\"b\":37},{\"tag\":\"incompatible\",\"a\":81,\"b\":39},{\"tag\":\"incompatible\",\"a\":81,\"b\":45},{\"tag\":\"incompatible\",\"a\":81,\"b\":64},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":21},{\"tag\":\"incompatible\",\"a\":82,\"b\":37},{\"tag\":\"incompatible\",\"a\":82,\"b\":38},{\"tag\":\"incompatible\",\"a\":82,\"b\":40},{\"tag\":\"incompatible\",\"a\":82,\"b\":71},{\"tag\":\"incompatible\",\"a\":82,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":25},{\"tag\":\"incompatible\",\"a\":83,\"b\":35},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":45},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":83,\"b\":73},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":84,\"b\":58},{\"tag\":\"incompatible\",\"a\":84,\"b\":66},{\"tag\":\"incompatible\",\"a\":85,\"b\":21},{\"tag\":\"incompatible\",\"a\":85,\"b\":22},{\"tag\":\"incompatible\",\"a\":85,\"b\":50},{\"tag\":\"incompatible\",\"a\":85,\"b\":70},{\"tag\":\"incompatible\",\"a\":85,\"b\":71},{\"tag\":\"incompatible\",\"a\":88,\"b\":17},{\"tag\":\"incompatible\",\"a\":88,\"b\":30},{\"tag\":\"incompatible\",\"a\":88,\"b\":53},{\"tag\":\"incompatible\",\"a\":88,\"b\":56},{\"tag\":\"incompatible\",\"a\":88,\"b\":69},{\"tag\":\"incompatible\",\"a\":88,\"b\":73},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":89,\"b\":58},{\"tag\":\"incompatible\",\"a\":89,\"b\":66},{\"tag\":\"incompatible\",\"a\":90,\"b\":39},{\"tag\":\"incompatible\",\"a\":90,\"b\":62},{\"tag\":\"incompatible\",\"a\":90,\"b\":64},{\"tag\":\"incompatible\",\"a\":90,\"b\":69},{\"tag\":\"incompatible\",\"a\":90,\"b\":79},{\"tag\":\"incompatible\",\"a\":90,\"b\":81},{\"tag\":\"incompatible\",\"a\":90,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"mate\",\"ridge\":7,\"a\":0,\"owners\":[1,20,21,22,23,24,26,28,29,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":25,\"owners\":[1,21,22,23,28,29,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":27,\"owners\":[1,20,22,23,26,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":30,\"owners\":[1,20,21,22,23,24,29,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":32,\"owners\":[0,20,21,24,25,26,27,28,30]},{\"tag\":\"mate\",\"ridge\":67,\"a\":25,\"owners\":[4,36,39,45,46]},{\"tag\":\"mate\",\"ridge\":67,\"a\":27,\"owners\":[4,34,39,44]},{\"tag\":\"mate\",\"ridge\":67,\"a\":31,\"owners\":[4,34,36,39,42,44,45]},{\"tag\":\"mate\",\"ridge\":67,\"a\":39,\"owners\":[0,25,27,31,42,46]},{\"tag\":\"mate\",\"ridge\":67,\"a\":44,\"owners\":[0,27,31,36,46]},{\"tag\":\"mate\",\"ridge\":67,\"a\":45,\"owners\":[0,25,31,34]},{\"tag\":\"mate\",\"ridge\":69,\"a\":30,\"owners\":[5,53,57,60]},{\"tag\":\"mate\",\"ridge\":69,\"a\":31,\"owners\":[5,53,56,57,59]},{\"tag\":\"mate\",\"ridge\":69,\"a\":53,\"owners\":[0,30,31]},{\"tag\":\"mate\",\"ridge\":69,\"a\":56,\"owners\":[0,27,31,60]},{\"tag\":\"mate\",\"ridge\":69,\"a\":57,\"owners\":[0,27,30,31,59,60]},{\"tag\":\"mate\",\"ridge\":70,\"a\":30,\"owners\":[12,73,77]},{\"tag\":\"mate\",\"ridge\":70,\"a\":31,\"owners\":[12,73,75,76]},{\"tag\":\"mate\",\"ridge\":70,\"a\":73,\"owners\":[0,30,31]},{\"tag\":\"mate\",\"ridge\":70,\"a\":76,\"owners\":[0,25,31]},{\"tag\":\"mate\",\"ridge\":70,\"a\":77,\"owners\":[0,25,30,75]},{\"tag\":\"mate\",\"ridge\":259,\"a\":31,\"owners\":[3,38,40,41,47]},{\"tag\":\"mate\",\"ridge\":259,\"a\":32,\"owners\":[3,38,40,46,47]},{\"tag\":\"mate\",\"ridge\":259,\"a\":40,\"owners\":[1,29,31,32,46]},{\"tag\":\"mate\",\"ridge\":259,\"a\":41,\"owners\":[1,29,31,46,47]},{\"tag\":\"mate\",\"ridge\":261,\"a\":7,\"owners\":[1,22,29,31,49,51,55,60]},{\"tag\":\"mate\",\"ridge\":261,\"a\":22,\"owners\":[7,55,58,60]},{\"tag\":\"mate\",\"ridge\":261,\"a\":31,\"owners\":[7,49,51,52,55,58]},{\"tag\":\"mate\",\"ridge\":261,\"a\":52,\"owners\":[1,29,31,55,60]},{\"tag\":\"mate\",\"ridge\":261,\"a\":58,\"owners\":[1,22,29,31,51,60]},{\"tag\":\"mate\",\"ridge\":262,\"a\":31,\"owners\":[13,71,72]},{\"tag\":\"mate\",\"ridge\":262,\"a\":32,\"owners\":[13,71,77]},{\"tag\":\"mate\",\"ridge\":262,\"a\":71,\"owners\":[1,31,32]},{\"tag\":\"mate\",\"ridge\":262,\"a\":77,\"owners\":[1,22,32,72]},{\"tag\":\"mate\",\"ridge\":11,\"a\":3,\"owners\":[2,20,21,23,33,34,35,36,37,39]},{\"tag\":\"mate\",\"ridge\":11,\"a\":37,\"owners\":[3,20,22,23,34,41]},{\"tag\":\"mate\",\"ridge\":11,\"a\":38,\"owners\":[2,20,23,34,35,39]},{\"tag\":\"mate\",\"ridge\":11,\"a\":39,\"owners\":[3,20,21,22,23,33,38,41]},{\"tag\":\"mate\",\"ridge\":131,\"a\":2,\"owners\":[4,26,28,30,43,44,45,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":30,\"owners\":[2,35,37,40,43,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":35,\"owners\":[4,28,30,45,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":40,\"owners\":[4,26,28,30,43,44,45]},{\"tag\":\"mate\",\"ridge\":131,\"a\":44,\"owners\":[2,28,37,40,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":45,\"owners\":[2,26,35,40]},{\"tag\":\"mate\",\"ridge\":137,\"a\":39,\"owners\":[8,62,65,68]},{\"tag\":\"mate\",\"ridge\":137,\"a\":40,\"owners\":[8,62,64,65,67]},{\"tag\":\"mate\",\"ridge\":137,\"a\":64,\"owners\":[2,37,40,68]},{\"tag\":\"mate\",\"ridge\":137,\"a\":65,\"owners\":[2,37,39,40,67,68]},{\"tag\":\"mate\",\"ridge\":138,\"a\":39,\"owners\":[14,79,82]},{\"tag\":\"mate\",\"ridge\":138,\"a\":40,\"owners\":[14,79,80,81]},{\"tag\":\"mate\",\"ridge\":138,\"a\":81,\"owners\":[2,35,40]},{\"tag\":\"mate\",\"ridge\":138,\"a\":82,\"owners\":[2,35,39,80]},{\"tag\":\"mate\",\"ridge\":265,\"a\":10,\"owners\":[3,22,38,40,49,51,63,68]},{\"tag\":\"mate\",\"ridge\":265,\"a\":40,\"owners\":[10,49,51,52,63,66]},{\"tag\":\"mate\",\"ridge\":265,\"a\":52,\"owners\":[3,38,40,63,68]},{\"tag\":\"mate\",\"ridge\":265,\"a\":66,\"owners\":[3,22,38,40,51,68]},{\"tag\":\"mate\",\"ridge\":266,\"a\":40,\"owners\":[15,71,72]},{\"tag\":\"mate\",\"ridge\":266,\"a\":71,\"owners\":[3,40,41]},{\"tag\":\"mate\",\"ridge\":266,\"a\":82,\"owners\":[3,22,41,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":30,\"owners\":[11,64,67,69]},{\"tag\":\"mate\",\"ridge\":193,\"a\":39,\"owners\":[11,56,59,69]},{\"tag\":\"mate\",\"ridge\":193,\"a\":45,\"owners\":[11,56,64]},{\"tag\":\"mate\",\"ridge\":193,\"a\":56,\"owners\":[4,39,45,67]},{\"tag\":\"mate\",\"ridge\":193,\"a\":64,\"owners\":[4,30,45,59]},{\"tag\":\"mate\",\"ridge\":193,\"a\":69,\"owners\":[4,30,39]},{\"tag\":\"mate\",\"ridge\":194,\"a\":30,\"owners\":[16,80,81,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":39,\"owners\":[16,75,76,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":44,\"owners\":[16,76,81]},{\"tag\":\"mate\",\"ridge\":194,\"a\":81,\"owners\":[4,30,44,75]},{\"tag\":\"mate\",\"ridge\":81,\"a\":25,\"owners\":[11,61,64,69]},{\"tag\":\"mate\",\"ridge\":81,\"a\":44,\"owners\":[5,53,57,61]},{\"tag\":\"mate\",\"ridge\":81,\"a\":53,\"owners\":[11,34,44,64]},{\"tag\":\"mate\",\"ridge\":81,\"a\":57,\"owners\":[11,34,42,44,61,64,69]},{\"tag\":\"mate\",\"ridge\":84,\"a\":25,\"owners\":[17,88]},{\"tag\":\"mate\",\"ridge\":84,\"a\":56,\"owners\":[17,73]},{\"tag\":\"mate\",\"ridge\":84,\"a\":57,\"owners\":[17,73,75,88]},{\"tag\":\"mate\",\"ridge\":84,\"a\":73,\"owners\":[5,56,57]},{\"tag\":\"mate\",\"ridge\":84,\"a\":88,\"owners\":[5,25,57]},{\"tag\":\"mate\",\"ridge\":517,\"a\":6,\"owners\":[7,23,32,52]},{\"tag\":\"mate\",\"ridge\":517,\"a\":32,\"owners\":[6,50,57]},{\"tag\":\"mate\",\"ridge\":517,\"a\":50,\"owners\":[7,32]},{\"tag\":\"mate\",\"ridge\":517,\"a\":57,\"owners\":[7,23,32,52]},{\"tag\":\"mate\",\"ridge\":529,\"a\":57,\"owners\":[9,65,66]},{\"tag\":\"mate\",\"ridge\":529,\"a\":58,\"owners\":[9,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":65,\"owners\":[6,57,58]},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[6,57]},{\"tag\":\"mate\",\"ridge\":532,\"a\":6,\"owners\":[85,86,89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":50,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[85,86,89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":58,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":769,\"a\":7,\"owners\":[10,41,66]},{\"tag\":\"mate\",\"ridge\":769,\"a\":32,\"owners\":[10,66]},{\"tag\":\"mate\",\"ridge\":769,\"a\":41,\"owners\":[7,58]},{\"tag\":\"mate\",\"ridge\":769,\"a\":58,\"owners\":[10,41]},{\"tag\":\"mate\",\"ridge\":769,\"a\":66,\"owners\":[7,32]},{\"tag\":\"mate\",\"ridge\":772,\"a\":7,\"owners\":[72,86,87,89]},{\"tag\":\"mate\",\"ridge\":772,\"a\":32,\"owners\":[86,87,89]},{\"tag\":\"mate\",\"ridge\":772,\"a\":52,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":772,\"a\":58,\"owners\":[72,87]},{\"tag\":\"mate\",\"ridge\":772,\"a\":87,\"owners\":[7,32,58]},{\"tag\":\"mate\",\"ridge\":772,\"a\":89,\"owners\":[7,32,52,72]},{\"tag\":\"mate\",\"ridge\":25,\"a\":66,\"owners\":[8,20,33,34,35,48,61,62,64]},{\"tag\":\"mate\",\"ridge\":145,\"a\":35,\"owners\":[11,54,56,69]},{\"tag\":\"mate\",\"ridge\":145,\"a\":62,\"owners\":[11,26,44,56]},{\"tag\":\"mate\",\"ridge\":145,\"a\":65,\"owners\":[11,26,43,44,54,56,69]},{\"tag\":\"mate\",\"ridge\":145,\"a\":69,\"owners\":[8,26,35,65]},{\"tag\":\"mate\",\"ridge\":152,\"a\":35,\"owners\":[18,90]},{\"tag\":\"mate\",\"ridge\":152,\"a\":64,\"owners\":[18,79]},{\"tag\":\"mate\",\"ridge\":152,\"a\":65,\"owners\":[18,79,80,90]},{\"tag\":\"mate\",\"ridge\":152,\"a\":90,\"owners\":[8,35,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":41,\"owners\":[9,50,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":50,\"owners\":[10,41]},{\"tag\":\"mate\",\"ridge\":521,\"a\":65,\"owners\":[10,23,41,52]},{\"tag\":\"mate\",\"ridge\":536,\"a\":9,\"owners\":[85,86,91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":50,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":65,\"owners\":[85,86,91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":66,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":536,\"a\":91,\"owners\":[9,50,65]},{\"tag\":\"mate\",\"ridge\":776,\"a\":10,\"owners\":[72,86,87,91]},{\"tag\":\"mate\",\"ridge\":776,\"a\":41,\"owners\":[86,87,91]},{\"tag\":\"mate\",\"ridge\":776,\"a\":52,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":776,\"a\":66,\"owners\":[72,87]},{\"tag\":\"mate\",\"ridge\":776,\"a\":91,\"owners\":[10,41,52,72]},{\"tag\":\"mate\",\"ridge\":208,\"a\":56,\"owners\":[19,80,83,90]},{\"tag\":\"mate\",\"ridge\":208,\"a\":64,\"owners\":[19,75,83,88]},{\"tag\":\"mate\",\"ridge\":208,\"a\":88,\"owners\":[11,44,64,80]},{\"tag\":\"mate\",\"ridge\":208,\"a\":90,\"owners\":[11,44,56,75]},{\"tag\":\"mate\",\"ridge\":38,\"a\":12,\"owners\":[13,21,24,28,29,70,71,74]},{\"tag\":\"mate\",\"ridge\":38,\"a\":27,\"owners\":[13,70,71,74]},{\"tag\":\"mate\",\"ridge\":38,\"a\":29,\"owners\":[12,70,73,74,76]},{\"tag\":\"mate\",\"ridge\":38,\"a\":71,\"owners\":[12,24,27,28,73,74,76]},{\"tag\":\"mate\",\"ridge\":38,\"a\":73,\"owners\":[13,21,28,29,71]},{\"tag\":\"mate\",\"ridge\":38,\"a\":76,\"owners\":[13,21,24,29,70,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":27,\"owners\":[16,78,81,83]},{\"tag\":\"mate\",\"ridge\":98,\"a\":45,\"owners\":[12,73,77,78]},{\"tag\":\"mate\",\"ridge\":98,\"a\":73,\"owners\":[16,36,45,46,81]},{\"tag\":\"mate\",\"ridge\":98,\"a\":77,\"owners\":[16,36,42,45,78,81,83]},{\"tag\":\"mate\",\"ridge\":98,\"a\":81,\"owners\":[12,27,42,46,73,77]},{\"tag\":\"mate\",\"ridge\":98,\"a\":83,\"owners\":[12,27,36,46,77]},{\"tag\":\"mate\",\"ridge\":100,\"a\":17,\"owners\":[12,27,59,60,76,77]},{\"tag\":\"mate\",\"ridge\":100,\"a\":27,\"owners\":[17,88]},{\"tag\":\"mate\",\"ridge\":100,\"a\":76,\"owners\":[17,53,60]},{\"tag\":\"mate\",\"ridge\":100,\"a\":77,\"owners\":[17,53,59,88]},{\"tag\":\"mate\",\"ridge\":100,\"a\":88,\"owners\":[12,27,60,77]},{\"tag\":\"mate\",\"ridge\":290,\"a\":15,\"owners\":[13,29,46,47,77]},{\"tag\":\"mate\",\"ridge\":290,\"a\":38,\"owners\":[13,77]},{\"tag\":\"mate\",\"ridge\":290,\"a\":77,\"owners\":[15,38,47,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":82,\"owners\":[13,29,46,77]},{\"tag\":\"mate\",\"ridge\":292,\"a\":71,\"owners\":[55,60,89]},{\"tag\":\"mate\",\"ridge\":292,\"a\":77,\"owners\":[51,55,84,87,89]},{\"tag\":\"mate\",\"ridge\":292,\"a\":87,\"owners\":[13,29,55,60,77]},{\"tag\":\"mate\",\"ridge\":42,\"a\":14,\"owners\":[15,21,33,36,38,70,71,78]},{\"tag\":\"mate\",\"ridge\":42,\"a\":37,\"owners\":[15,70,71,78]},{\"tag\":\"mate\",\"ridge\":42,\"a\":38,\"owners\":[14,70,78,79,81]},{\"tag\":\"mate\",\"ridge\":42,\"a\":71,\"owners\":[14,33,36,37,78,79,81]},{\"tag\":\"mate\",\"ridge\":42,\"a\":79,\"owners\":[15,21,36,38,71]},{\"tag\":\"mate\",\"ridge\":42,\"a\":81,\"owners\":[15,21,33,38,70,71]},{\"tag\":\"mate\",\"ridge\":162,\"a\":45,\"owners\":[14,74,79,82]},{\"tag\":\"mate\",\"ridge\":162,\"a\":79,\"owners\":[16,28,45,47,76]},{\"tag\":\"mate\",\"ridge\":162,\"a\":82,\"owners\":[16,28,43,45,74,76,83]},{\"tag\":\"mate\",\"ridge\":162,\"a\":83,\"owners\":[14,28,37,47,82]},{\"tag\":\"mate\",\"ridge\":168,\"a\":18,\"owners\":[14,37,67,68,81,82]},{\"tag\":\"mate\",\"ridge\":168,\"a\":37,\"owners\":[18,90]},{\"tag\":\"mate\",\"ridge\":168,\"a\":81,\"owners\":[18,62,68]},{\"tag\":\"mate\",\"ridge\":168,\"a\":82,\"owners\":[18,62,67,90]},{\"tag\":\"mate\",\"ridge\":168,\"a\":90,\"owners\":[14,37,68,82]},{\"tag\":\"mate\",\"ridge\":296,\"a\":71,\"owners\":[63,68,91]},{\"tag\":\"mate\",\"ridge\":296,\"a\":87,\"owners\":[15,38,63,68,82]},{\"tag\":\"mate\",\"ridge\":224,\"a\":45,\"owners\":[19,88,90]},{\"tag\":\"mate\",\"ridge\":224,\"a\":69,\"owners\":[16,76,81]},{\"tag\":\"mate\",\"ridge\":224,\"a\":76,\"owners\":[19,67,69,90]},{\"tag\":\"mate\",\"ridge\":224,\"a\":81,\"owners\":[19,59,69,88]},{\"tag\":\"mate\",\"ridge\":224,\"a\":88,\"owners\":[16,45,67,81]},{\"tag\":\"mate\",\"ridge\":224,\"a\":90,\"owners\":[16,45,59,76]},{\"tag\":\"mate\",\"ridge\":52,\"a\":17,\"owners\":[24,48,54,55,70,74,84,85,89]},{\"tag\":\"mate\",\"ridge\":52,\"a\":53,\"owners\":[70,74,84,85,89]},{\"tag\":\"mate\",\"ridge\":52,\"a\":73,\"owners\":[48,54,55,84,85,89]},{\"tag\":\"mate\",\"ridge\":52,\"a\":85,\"owners\":[17,24,53,54,55,73,74,88]},{\"tag\":\"mate\",\"ridge\":52,\"a\":88,\"owners\":[24,48,55,70,84,85,89]},{\"tag\":\"mate\",\"ridge\":112,\"a\":53,\"owners\":[19,78,83,90]},{\"tag\":\"mate\",\"ridge\":112,\"a\":69,\"owners\":[17,73,78]},{\"tag\":\"mate\",\"ridge\":112,\"a\":83,\"owners\":[17,53,61]},{\"tag\":\"mate\",\"ridge\":112,\"a\":90,\"owners\":[17,42,53,73]},{\"tag\":\"mate\",\"ridge\":56,\"a\":79,\"owners\":[48,61,63,84,85,91]},{\"tag\":\"mate\",\"ridge\":56,\"a\":85,\"owners\":[18,33,61,62,63,78,79,90]},{\"tag\":\"mate\",\"ridge\":56,\"a\":91,\"owners\":[18,33,48,61,62,70,78,79,90]},{\"tag\":\"mate\",\"ridge\":176,\"a\":69,\"owners\":[18,74,79]},{\"tag\":\"mate\",\"ridge\":176,\"a\":79,\"owners\":[19,54,69,88]},{\"tag\":\"mate\",\"ridge\":176,\"a\":83,\"owners\":[18,54,62]},{\"tag\":\"mate\",\"ridge\":176,\"a\":88,\"owners\":[18,43,62,79]},{\"tag\":\"mate\",\"ridge\":30,\"a\":20,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":30,\"a\":70,\"owners\":[20]},{\"tag\":\"mate\",\"ridge\":45,\"a\":21,\"owners\":[48,51]},{\"tag\":\"mate\",\"ridge\":45,\"a\":48,\"owners\":[21,51]},{\"tag\":\"mate\",\"ridge\":45,\"a\":51,\"owners\":[21,48]},{\"tag\":\"mate\",\"ridge\":526,\"a\":23,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":526,\"a\":72,\"owners\":[23]},{\"tag\":\"mate\",\"ridge\":51,\"a\":24,\"owners\":[33,42,43]},{\"tag\":\"mate\",\"ridge\":51,\"a\":33,\"owners\":[24,42,43]},{\"tag\":\"mate\",\"ridge\":51,\"a\":42,\"owners\":[24,33,43]},{\"tag\":\"mate\",\"ridge\":51,\"a\":43,\"owners\":[24,33,42]},{\"tag\":\"mate\",\"ridge\":150,\"a\":26,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":150,\"a\":74,\"owners\":[26,75]},{\"tag\":\"mate\",\"ridge\":150,\"a\":75,\"owners\":[26,74]},{\"tag\":\"mate\",\"ridge\":165,\"a\":28,\"owners\":[54,59]},{\"tag\":\"mate\",\"ridge\":165,\"a\":54,\"owners\":[28,59]},{\"tag\":\"mate\",\"ridge\":165,\"a\":59,\"owners\":[28,54]},{\"tag\":\"mate\",\"ridge\":90,\"a\":34,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":90,\"a\":78,\"owners\":[34,80]},{\"tag\":\"mate\",\"ridge\":90,\"a\":80,\"owners\":[34,78]},{\"tag\":\"mate\",\"ridge\":105,\"a\":36,\"owners\":[61,67]},{\"tag\":\"mate\",\"ridge\":105,\"a\":61,\"owners\":[36,67]},{\"tag\":\"mate\",\"ridge\":105,\"a\":67,\"owners\":[36,61]},{\"tag\":\"mate\",\"ridge\":353,\"a\":46,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":353,\"a\":60,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":417,\"a\":47,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":417,\"a\":68,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":284,\"a\":86,\"owners\":[49,84]},{\"tag\":\"mate\",\"ridge\":305,\"a\":55,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":305,\"a\":63,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":556,\"a\":85,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":556,\"a\":87,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":816,\"a\":89,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":816,\"a\":91,\"owners\":[89]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,93]},{\"tag\":\"group_take\",\"kind\":1,\"index\":1,\"member\":1,\"full_literals\":[-2,94]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-3,95]},{\"tag\":\"group_take\",\"kind\":1,\"index\":3,\"member\":3,\"full_literals\":[-4,96]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-5,97]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-6,98]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-7,99]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-8,100]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-9,101]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-10,102]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-11,103]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-12,104]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-13,105]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-14,106]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-15,107]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-16,108]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-17,109]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-18,110]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-19,111]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-20,112]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-94,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-115,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-95,-115,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-116,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-117,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-113,false,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-113,-116,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-113,-117,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-114,false,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-114,-116,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-99,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-98,-99,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-102,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-101,false,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-101,-102,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-123,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-124,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-100,-123,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-125,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-126,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-121,false,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-121,-125,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-122,false,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-127,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-128,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-118,false,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-118,-127,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-118,-128,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-119,false,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-119,-127,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-120,false,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-120,-127,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-104,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-103,false,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-103,-104,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-107,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-106,false,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-135,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-105,-135,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-136,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-137,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-133,false,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-133,-136,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-133,-137,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-134,false,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-134,-136,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-109,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-108,false,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-108,-109,142],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-112,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-111,false,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-111,-112,144],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-143,145],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-144,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,145],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-143,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-145,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-146,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-141,false,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-141,-145,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-141,-146,149],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-142,false,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-142,-145,149],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-147,150],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-148,151],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-149,152],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-138,false,150],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-138,-147,151],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-138,-148,152],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-138,-149,153],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-139,false,151],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-139,-147,152],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-139,-148,153],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-139,-149,154],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-140,-147,153],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-140,-148,154],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":5,\"direction\":\"forward\",\"full_literals\":[false,-154,155],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-129,-153,155],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-130,-152,155],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-131,-151,155],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":4,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-132,-150,155],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[50,57,58],\"full_literals\":[-156,51,58,59]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":57,\"full_literals\":[-58,156]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":58,\"full_literals\":[-59,156]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[65,66],\"full_literals\":[-157,66,67]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":65,\"full_literals\":[-66,157]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":66,\"full_literals\":[-67,157]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[22,32,41,52],\"full_literals\":[-158,23,33,42,53]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":32,\"full_literals\":[-33,158]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":41,\"full_literals\":[-42,158]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":52,\"full_literals\":[-53,158]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[27,29,31,77],\"full_literals\":[-159,28,30,32,78]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":27,\"full_literals\":[-28,159]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":29,\"full_literals\":[-30,159]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":31,\"full_literals\":[-32,159]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":77,\"full_literals\":[-78,159]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[38,71,82],\"full_literals\":[-160,39,72,83]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":71,\"full_literals\":[-72,160]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":82,\"full_literals\":[-83,160]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[30,56,76,88],\"full_literals\":[-161,31,57,77,89]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":30,\"full_literals\":[-31,161]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":56,\"full_literals\":[-57,161]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":76,\"full_literals\":[-77,161]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":88,\"full_literals\":[-89,161]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[35,37,39,40],\"full_literals\":[-162,36,38,40,41]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":37,\"full_literals\":[-38,162]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":39,\"full_literals\":[-40,162]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":40,\"full_literals\":[-41,162]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[45,53,62,69],\"full_literals\":[-163,46,54,63,70]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":45,\"full_literals\":[-46,163]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":53,\"full_literals\":[-54,163]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":62,\"full_literals\":[-63,163]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":69,\"full_literals\":[-70,163]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[25,44,73,79,83],\"full_literals\":[-164,26,45,74,80,84]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":44,\"full_literals\":[-45,164]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":73,\"full_literals\":[-74,164]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":79,\"full_literals\":[-80,164]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[64,81,90],\"full_literals\":[-165,65,82,91]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":64,\"full_literals\":[-65,165]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":81,\"full_literals\":[-82,165]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":90,\"full_literals\":[-91,165]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-166,156,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-167,156,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-167,false,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-156,-157,167],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-168,159,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-160,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-169,159,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-159,false,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-169,false,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-159,-160,169],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-170,158,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-171,158,169],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-172,158,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-171,false,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-158,-168,171],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-172,false,169],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-158,-169,172],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-173,166,172],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-174,166,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-173,167,171],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-174,167,172],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-175,167,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-173,false,170],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-174,false,171],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-167,-171,174],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-175,false,172],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-167,-172,175],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-176,161,162],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-177,161,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-161,false,176],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-177,false,162],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-161,-162,177],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-178,164,165],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-165,178],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-179,164,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-164,false,178],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-179,false,165],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-164,-165,179],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-180,163,178],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-181,163,179],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-179,181],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-182,163,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-181,false,178],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-163,-178,181],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-182,false,179],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-163,-179,182],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-183,176,182],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-184,176,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-183,177,181],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-184,177,182],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-176,-182,184],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-185,177,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-183,false,180],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-184,false,181],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-177,-181,184],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-185,false,182],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-177,-182,185],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-186,173,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-186,174,185],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-186,175,184],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"forward\",\"full_literals\":[-174,-185,187],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-186,false,183],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-175,-184,187],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-50,188]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":85,\"full_literals\":[-86,188]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":89,\"full_literals\":[-90,188]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-85,189]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-88,189]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":91,\"full_literals\":[-92,189]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":21,\"full_literals\":[-22,190]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-87,190]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":48,\"full_literals\":[-49,191]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-73,191]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":24,\"full_literals\":[-25,192]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":26,\"full_literals\":[-27,192]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":34,\"full_literals\":[-35,192]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[33,74,78],\"full_literals\":[-193,34,75,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":33,\"full_literals\":[-34,193]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-75,193]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-79,193]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[42,75,80],\"full_literals\":[-194,43,76,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":42,\"full_literals\":[-43,194]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-76,194]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-81,194]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[28,36,43,46,47,51,55],\"full_literals\":[-195,29,37,44,47,48,52,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":28,\"full_literals\":[-29,195]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":36,\"full_literals\":[-37,195]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":43,\"full_literals\":[-44,195]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":46,\"full_literals\":[-47,195]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":47,\"full_literals\":[-48,195]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":51,\"full_literals\":[-52,195]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":55,\"full_literals\":[-56,195]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[54,60,61,63,68],\"full_literals\":[-196,55,61,62,64,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":54,\"full_literals\":[-55,196]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":60,\"full_literals\":[-61,196]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":61,\"full_literals\":[-62,196]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":63,\"full_literals\":[-64,196]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":68,\"full_literals\":[-69,196]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[59,67],\"full_literals\":[-197,60,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":59,\"full_literals\":[-60,197]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":67,\"full_literals\":[-68,197]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0059\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-189,198],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0059\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-188,false,198],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0067\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-192,199],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0067\",\"joined_name\":\"grouped3_0066\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-191,false,199],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0064\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-199,200],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0064\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-190,false,200],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0059\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0060\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-200,201],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0059\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0060\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-198,false,201],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0059\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0060\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-198,-200,202],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0069\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-203,193,194],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0069\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-194,203],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0069\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-193,false,203],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0069\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-193,-194,204],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-205,196,197],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-197,205],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-196,false,205],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-196,-197,206],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-207,195,205],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-206,208],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-195,false,207],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-195,-205,208],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-209,203,207],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-207,209],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-208,210],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-203,false,209],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-203,-207,210],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0070\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-204,false,210],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-201,-210,211],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-202,-209,211],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[0,9,10,15,32,40,45,57,64,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[0,9,10,15,32,40,44,57,62,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[0,9,10,15,32,40,45,57,64,77,79,84,86,88]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[0,9,10,15,32,40,44,57,62,77,81,84,86,88]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[5,6,10,18,27,32,40,44,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[5,6,10,18,30,32,40,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[5,6,7,17,31,39,41,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[6,7,11,19,31,39,41,53,65,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[5,6,7,17,31,37,41,44,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[0,6,10,14,32,40,44,53,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[0,1,9,15,40,44,52,57,62,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[0,9,10,15,32,40,44,57,62,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[6,13,14,15,31,40,44,52,53,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[0,9,10,12,32,40,44,57,62,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[6,7,10,14,31,40,44,53,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[0,6,10,14,32,40,45,56,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[0,1,9,15,40,45,52,57,64,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[0,9,10,15,32,40,45,57,64,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[6,13,14,15,31,40,45,52,56,65,73,89,90,91]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[0,9,10,12,32,40,45,57,64,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[6,7,10,14,31,40,45,56,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[4,6,7,16,31,37,41,56,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[6,15,16,19,30,32,40,53,64,66,77,79,85,87]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[6,14,15,18,30,32,40,53,64,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[6,14,15,18,25,32,40,45,64,66,77,85,87,88]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[0,5,6,15,32,40,45,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[4,6,11,15,25,32,40,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[0,5,6,15,32,40,44,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[1,9,11,16,30,35,41,53,58,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[0,3,6,17,32,39,56,62,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[0,1,9,17,35,41,45,56,58,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[0,1,9,17,39,41,56,58,62,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":32,\"vertices\":[0,3,6,17,32,35,45,56,66,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":33,\"vertices\":[1,9,11,16,25,39,41,58,62,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":34,\"vertices\":[7,12,13,17,31,35,41,45,50,56,82,89,90,91]},{\"tag\":\"block\",\"leaf\":35,\"vertices\":[0,5,10,15,32,40,45,50,64,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":36,\"vertices\":[7,13,16,19,31,39,41,50,56,62,73,82,89,91]},{\"tag\":\"block\",\"leaf\":37,\"vertices\":[7,12,13,17,31,39,41,50,56,62,82,83,89,91]},{\"tag\":\"block\",\"leaf\":38,\"vertices\":[4,7,11,13,31,35,41,50,53,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":39,\"vertices\":[0,5,10,15,32,40,44,50,62,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":40,\"vertices\":[1,7,11,16,30,35,41,50,53,77,82,89,90,91]},{\"tag\":\"block\",\"leaf\":41,\"vertices\":[0,3,10,17,32,39,50,56,62,77,82,83,89,91]},{\"tag\":\"block\",\"leaf\":42,\"vertices\":[0,1,7,17,35,41,45,50,56,77,82,89,90,91]},{\"tag\":\"block\",\"leaf\":43,\"vertices\":[0,1,7,17,39,41,50,56,62,77,82,83,89,91]},{\"tag\":\"block\",\"leaf\":44,\"vertices\":[0,3,10,17,32,35,45,50,56,77,82,89,90,91]},{\"tag\":\"block\",\"leaf\":45,\"vertices\":[1,7,11,16,25,39,41,50,62,77,82,88,89,91]},{\"tag\":\"block\",\"leaf\":46,\"vertices\":[7,13,15,17,31,37,41,44,57,65,76,85,87,90]},{\"tag\":\"block\",\"leaf\":47,\"vertices\":[7,13,15,17,31,39,41,57,65,69,76,79,85,87]},{\"tag\":\"block\",\"leaf\":48,\"vertices\":[0,10,15,18,32,40,44,57,65,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":49,\"vertices\":[0,2,7,17,29,41,44,57,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":50,\"vertices\":[0,10,11,15,32,40,45,57,65,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":51,\"vertices\":[0,10,11,16,32,38,39,57,65,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":52,\"vertices\":[7,13,17,18,31,39,41,57,65,69,76,82,85,87]},{\"tag\":\"block\",\"leaf\":53,\"vertices\":[7,13,16,18,31,39,41,57,65,69,73,82,85,87]},{\"tag\":\"block\",\"leaf\":54,\"vertices\":[7,13,15,17,31,37,41,44,57,65,76,84,86,90]},{\"tag\":\"block\",\"leaf\":55,\"vertices\":[7,13,15,17,31,39,41,57,65,69,76,79,84,86]},{\"tag\":\"block\",\"leaf\":56,\"vertices\":[0,10,15,18,32,40,44,57,65,77,81,84,86,88]},{\"tag\":\"block\",\"leaf\":57,\"vertices\":[0,2,7,17,29,41,44,57,65,76,82,84,86,90]},{\"tag\":\"block\",\"leaf\":58,\"vertices\":[0,10,11,15,32,40,45,57,65,77,79,84,86,88]},{\"tag\":\"block\",\"leaf\":59,\"vertices\":[0,10,11,16,32,38,39,57,65,77,79,84,86,88]},{\"tag\":\"block\",\"leaf\":60,\"vertices\":[7,13,17,18,31,39,41,57,65,69,76,82,84,86]},{\"tag\":\"block\",\"leaf\":61,\"vertices\":[7,13,16,18,31,39,41,57,65,69,73,82,84,86]},{\"tag\":\"block\",\"leaf\":62,\"vertices\":[7,17,18,19,31,37,41,44,57,65,71,76,89,91]},{\"tag\":\"block\",\"leaf\":63,\"vertices\":[7,14,17,18,31,39,41,57,65,69,71,76,89,91]},{\"tag\":\"block\",\"leaf\":64,\"vertices\":[1,15,17,18,30,40,52,57,65,69,77,81,89,91]},{\"tag\":\"block\",\"leaf\":65,\"vertices\":[7,13,17,18,31,39,41,57,65,69,76,82,89,91]},{\"tag\":\"block\",\"leaf\":66,\"vertices\":[11,13,17,19,31,38,39,52,57,65,76,79,89,91]},{\"tag\":\"block\",\"leaf\":67,\"vertices\":[7,11,17,19,31,39,41,57,65,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":68,\"vertices\":[1,15,16,17,30,40,52,57,65,69,77,79,89,91]},{\"tag\":\"block\",\"leaf\":69,\"vertices\":[7,13,16,18,31,39,41,57,65,69,73,82,89,91]},{\"tag\":\"block\",\"leaf\":70,\"vertices\":[4,13,15,17,31,40,52,57,65,69,76,79,89,91]},{\"tag\":\"block\",\"leaf\":71,\"vertices\":[1,13,15,18,30,40,52,57,65,69,73,81,89,91]},{\"tag\":\"block\",\"leaf\":72,\"vertices\":[7,13,15,17,31,39,41,57,65,69,76,79,89,91]},{\"tag\":\"block\",\"leaf\":73,\"vertices\":[7,12,16,17,31,39,41,57,65,69,71,79,89,91]},{\"tag\":\"block\",\"leaf\":74,\"vertices\":[7,14,16,18,31,39,41,57,65,69,71,73,89,91]},{\"tag\":\"block\",\"leaf\":75,\"vertices\":[0,1,7,17,39,41,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":76,\"vertices\":[0,4,10,17,32,40,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":77,\"vertices\":[0,3,10,17,32,39,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":78,\"vertices\":[0,4,10,18,32,40,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":79,\"vertices\":[4,7,10,17,31,40,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":80,\"vertices\":[1,7,10,18,30,40,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":81,\"vertices\":[4,7,11,17,31,37,41,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":82,\"vertices\":[7,12,16,18,31,37,41,44,57,65,71,88,89,91]},{\"tag\":\"block\",\"leaf\":83,\"vertices\":[7,12,16,17,31,37,41,44,57,65,71,89,90,91]},{\"tag\":\"block\",\"leaf\":84,\"vertices\":[0,1,2,18,38,44,52,57,65,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":85,\"vertices\":[0,2,7,17,29,41,44,57,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":86,\"vertices\":[0,14,15,17,29,40,44,52,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":87,\"vertices\":[0,1,7,17,37,41,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":88,\"vertices\":[0,10,14,17,32,40,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":89,\"vertices\":[0,3,10,17,32,37,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":90,\"vertices\":[0,10,15,18,32,40,44,57,65,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":91,\"vertices\":[7,13,15,17,31,37,41,44,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":92,\"vertices\":[0,1,15,18,40,44,52,57,65,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":93,\"vertices\":[0,12,15,18,29,40,44,52,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":94,\"vertices\":[1,13,15,18,27,40,44,52,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":95,\"vertices\":[12,13,15,18,31,40,44,52,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":96,\"vertices\":[0,10,12,18,32,40,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":97,\"vertices\":[7,10,12,18,31,40,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":98,\"vertices\":[1,7,10,18,27,40,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":99,\"vertices\":[4,7,11,16,31,37,41,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":100,\"vertices\":[0,1,11,16,38,39,52,57,65,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":101,\"vertices\":[0,10,11,16,32,38,39,57,65,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":102,\"vertices\":[11,12,13,16,31,38,39,52,57,65,79,88,89,91]},{\"tag\":\"block\",\"leaf\":103,\"vertices\":[1,7,11,16,30,37,41,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":104,\"vertices\":[7,11,12,16,31,39,41,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":105,\"vertices\":[1,7,11,16,27,39,41,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":106,\"vertices\":[0,1,11,15,40,45,52,57,65,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":107,\"vertices\":[0,10,11,15,32,40,45,57,65,77,79,88,89,91]},{\"tag\":\"block\",\"leaf\":108,\"vertices\":[11,12,13,15,31,40,45,52,57,65,79,88,89,91]},{\"tag\":\"block\",\"leaf\":109,\"vertices\":[0,10,11,12,32,40,45,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":110,\"vertices\":[0,10,11,14,32,40,45,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":111,\"vertices\":[7,10,11,12,31,40,45,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":112,\"vertices\":[7,12,13,15,31,40,45,57,64,66,79,85,87,88]},{\"tag\":\"block\",\"leaf\":113,\"vertices\":[7,12,13,15,31,40,44,57,62,66,81,85,87,88]},{\"tag\":\"block\",\"leaf\":114,\"vertices\":[0,1,7,15,40,45,57,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":115,\"vertices\":[0,1,7,15,40,44,57,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":116,\"vertices\":[4,13,15,16,27,32,40,57,64,66,79,85,87,88]},{\"tag\":\"block\",\"leaf\":117,\"vertices\":[0,12,13,15,32,40,45,57,64,66,79,85,87,88]},{\"tag\":\"block\",\"leaf\":118,\"vertices\":[5,13,15,17,31,37,41,44,58,65,76,85,87,90]},{\"tag\":\"block\",\"leaf\":119,\"vertices\":[0,12,13,15,32,40,44,57,62,66,81,85,87,88]},{\"tag\":\"block\",\"leaf\":120,\"vertices\":[11,13,15,19,30,32,40,57,62,66,73,81,85,87]},{\"tag\":\"block\",\"leaf\":121,\"vertices\":[5,13,15,17,31,39,41,58,65,69,76,79,85,87]},{\"tag\":\"block\",\"leaf\":122,\"vertices\":[0,15,17,19,32,40,45,57,64,66,77,79,85,87]},{\"tag\":\"block\",\"leaf\":123,\"vertices\":[0,15,17,19,32,40,44,57,62,66,77,81,85,87]},{\"tag\":\"block\",\"leaf\":124,\"vertices\":[0,3,11,17,32,35,45,57,66,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":125,\"vertices\":[0,3,11,17,32,39,57,62,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":126,\"vertices\":[0,8,15,18,32,40,44,57,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":127,\"vertices\":[0,2,5,17,29,41,44,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":128,\"vertices\":[0,3,11,18,32,35,45,57,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":129,\"vertices\":[0,4,11,18,32,35,38,57,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":130,\"vertices\":[0,14,15,18,32,40,45,57,64,66,77,85,87,88]},{\"tag\":\"block\",\"leaf\":131,\"vertices\":[0,1,2,17,41,45,56,58,65,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":132,\"vertices\":[0,3,11,16,32,39,57,62,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":133,\"vertices\":[0,4,11,15,32,40,57,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":134,\"vertices\":[0,14,15,16,32,40,44,57,62,66,77,85,87,88]},{\"tag\":\"block\",\"leaf\":135,\"vertices\":[0,1,2,16,41,44,53,58,65,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":136,\"vertices\":[0,1,2,13,41,44,53,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":137,\"vertices\":[0,8,11,15,32,40,45,57,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":138,\"vertices\":[0,8,11,16,32,38,39,57,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":139,\"vertices\":[0,4,15,16,32,40,57,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":140,\"vertices\":[0,1,2,13,41,45,56,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":141,\"vertices\":[0,2,4,16,29,41,56,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":142,\"vertices\":[1,11,16,18,25,39,41,58,65,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":143,\"vertices\":[11,17,18,19,25,29,39,41,58,65,76,82,85,87]},{\"tag\":\"block\",\"leaf\":144,\"vertices\":[11,12,16,18,25,29,39,41,58,65,82,85,87,88]},{\"tag\":\"block\",\"leaf\":145,\"vertices\":[11,13,18,19,31,39,41,53,58,65,76,82,85,87]},{\"tag\":\"block\",\"leaf\":146,\"vertices\":[11,12,13,18,31,39,41,53,58,65,82,83,85,87]},{\"tag\":\"block\",\"leaf\":147,\"vertices\":[0,1,11,18,39,41,53,58,65,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":148,\"vertices\":[0,1,17,18,39,41,56,58,65,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":149,\"vertices\":[0,12,17,18,29,39,41,56,58,65,82,83,85,87]},{\"tag\":\"block\",\"leaf\":150,\"vertices\":[1,13,17,18,27,39,41,56,58,65,82,83,85,87]},{\"tag\":\"block\",\"leaf\":151,\"vertices\":[12,13,17,18,31,39,41,56,58,65,82,83,85,87]},{\"tag\":\"block\",\"leaf\":152,\"vertices\":[13,16,18,19,31,39,41,56,58,65,73,82,85,87]},{\"tag\":\"block\",\"leaf\":153,\"vertices\":[0,16,18,19,29,39,41,56,58,65,73,82,85,87]},{\"tag\":\"block\",\"leaf\":154,\"vertices\":[5,13,17,18,31,39,41,58,65,69,76,82,85,87]},{\"tag\":\"block\",\"leaf\":155,\"vertices\":[5,13,16,18,31,39,41,58,65,69,73,82,85,87]},{\"tag\":\"block\",\"leaf\":156,\"vertices\":[1,16,17,18,25,39,41,58,65,69,77,82,85,87]},{\"tag\":\"block\",\"leaf\":157,\"vertices\":[1,13,17,18,25,39,41,58,65,69,76,82,85,87]},{\"tag\":\"block\",\"leaf\":158,\"vertices\":[2,6,7,13,31,41,45,56,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":159,\"vertices\":[2,6,7,13,31,41,44,53,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":160,\"vertices\":[2,6,7,13,31,41,45,56,65,73,82,84,86,90]},{\"tag\":\"block\",\"leaf\":161,\"vertices\":[2,6,7,13,31,41,44,53,65,76,82,84,86,90]},{\"tag\":\"block\",\"leaf\":162,\"vertices\":[7,8,9,17,31,37,41,44,57,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":163,\"vertices\":[7,8,9,17,31,39,41,57,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":164,\"vertices\":[8,9,10,18,30,32,40,57,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":165,\"vertices\":[9,10,11,19,30,32,40,57,62,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":166,\"vertices\":[8,9,10,18,27,32,40,44,57,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":167,\"vertices\":[2,7,9,12,31,41,44,57,62,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":168,\"vertices\":[2,3,6,13,31,44,52,53,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":169,\"vertices\":[2,6,7,13,31,41,44,53,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":170,\"vertices\":[9,12,13,15,31,40,44,52,57,62,81,88,89,91]},{\"tag\":\"block\",\"leaf\":171,\"vertices\":[2,6,7,14,31,41,44,53,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":172,\"vertices\":[7,9,10,12,31,40,44,57,62,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":173,\"vertices\":[2,7,9,12,31,41,45,57,64,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":174,\"vertices\":[2,3,6,13,31,45,52,56,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":175,\"vertices\":[2,6,7,13,31,41,45,56,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":176,\"vertices\":[9,12,13,15,31,40,45,52,57,64,79,88,89,91]},{\"tag\":\"block\",\"leaf\":177,\"vertices\":[2,6,7,14,31,41,45,56,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":178,\"vertices\":[7,9,10,12,31,40,45,57,64,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":179,\"vertices\":[4,9,10,16,27,32,40,57,64,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":180,\"vertices\":[9,13,16,19,31,39,41,56,58,62,73,82,85,87]},{\"tag\":\"block\",\"leaf\":181,\"vertices\":[9,12,13,17,31,39,41,56,58,62,82,83,85,87]},{\"tag\":\"block\",\"leaf\":182,\"vertices\":[9,12,13,17,31,35,41,45,56,58,82,85,87,90]},{\"tag\":\"block\",\"leaf\":183,\"vertices\":[2,8,9,13,31,41,45,56,58,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":184,\"vertices\":[4,9,11,13,31,35,41,53,58,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":185,\"vertices\":[2,8,9,13,31,41,44,53,58,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":186,\"vertices\":[3,6,11,16,25,32,39,62,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":187,\"vertices\":[1,2,9,18,30,41,53,58,64,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":188,\"vertices\":[2,3,6,18,25,32,45,64,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":189,\"vertices\":[2,3,6,18,30,32,53,64,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":190,\"vertices\":[1,2,9,18,25,41,45,58,64,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":191,\"vertices\":[3,6,11,16,30,32,35,53,66,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":192,\"vertices\":[10,14,15,18,25,32,40,45,50,64,77,88,89,91]},{\"tag\":\"block\",\"leaf\":193,\"vertices\":[2,7,8,13,31,41,45,50,56,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":194,\"vertices\":[10,15,16,19,30,32,40,50,53,64,77,79,89,91]},{\"tag\":\"block\",\"leaf\":195,\"vertices\":[10,14,15,18,30,32,40,50,53,64,77,83,89,91]},{\"tag\":\"block\",\"leaf\":196,\"vertices\":[4,10,11,15,25,32,40,50,62,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":197,\"vertices\":[2,7,8,13,31,41,44,50,53,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":198,\"vertices\":[3,10,11,16,25,32,39,50,62,77,82,88,89,91]},{\"tag\":\"block\",\"leaf\":199,\"vertices\":[1,2,7,18,30,41,50,53,64,77,82,83,89,91]},{\"tag\":\"block\",\"leaf\":200,\"vertices\":[2,3,10,18,25,32,45,50,64,77,82,88,89,91]},{\"tag\":\"block\",\"leaf\":201,\"vertices\":[2,3,10,18,30,32,50,53,64,77,82,83,89,91]},{\"tag\":\"block\",\"leaf\":202,\"vertices\":[1,2,7,18,25,41,45,50,64,77,82,88,89,91]},{\"tag\":\"block\",\"leaf\":203,\"vertices\":[3,10,11,16,30,32,35,50,53,77,82,89,90,91]},{\"tag\":\"block\",\"leaf\":204,\"vertices\":[10,13,15,18,27,32,40,44,57,65,81,85,87,88]},{\"tag\":\"block\",\"leaf\":205,\"vertices\":[10,13,15,18,30,32,40,57,65,69,73,81,85,87]},{\"tag\":\"block\",\"leaf\":206,\"vertices\":[2,7,13,17,31,41,44,57,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":207,\"vertices\":[0,2,10,18,32,38,44,57,65,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":208,\"vertices\":[2,7,11,13,31,41,45,57,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":209,\"vertices\":[2,7,11,16,29,30,41,57,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":210,\"vertices\":[10,15,17,18,30,32,40,57,65,69,77,81,85,87]},{\"tag\":\"block\",\"leaf\":211,\"vertices\":[10,15,16,17,30,32,40,57,65,69,77,79,85,87]},{\"tag\":\"block\",\"leaf\":212,\"vertices\":[10,13,15,18,27,32,40,44,57,65,81,84,86,88]},{\"tag\":\"block\",\"leaf\":213,\"vertices\":[10,13,15,18,30,32,40,57,65,69,73,81,84,86]},{\"tag\":\"block\",\"leaf\":214,\"vertices\":[2,7,13,17,31,41,44,57,65,76,82,84,86,90]},{\"tag\":\"block\",\"leaf\":215,\"vertices\":[0,2,10,18,32,38,44,57,65,77,81,84,86,88]},{\"tag\":\"block\",\"leaf\":216,\"vertices\":[2,7,11,13,31,41,45,57,65,73,82,84,86,90]},{\"tag\":\"block\",\"leaf\":217,\"vertices\":[2,7,11,16,29,30,41,57,65,73,82,84,86,90]},{\"tag\":\"block\",\"leaf\":218,\"vertices\":[10,15,17,18,30,32,40,57,65,69,77,81,84,86]},{\"tag\":\"block\",\"leaf\":219,\"vertices\":[10,15,16,17,30,32,40,57,65,69,77,79,84,86]},{\"tag\":\"block\",\"leaf\":220,\"vertices\":[10,17,18,19,27,32,40,44,57,65,71,81,89,91]},{\"tag\":\"block\",\"leaf\":221,\"vertices\":[10,12,17,18,30,32,40,57,65,69,71,81,89,91]},{\"tag\":\"block\",\"leaf\":222,\"vertices\":[3,13,17,18,31,39,52,57,65,69,76,82,89,91]},{\"tag\":\"block\",\"leaf\":223,\"vertices\":[10,15,17,18,30,32,40,57,65,69,77,81,89,91]},{\"tag\":\"block\",\"leaf\":224,\"vertices\":[11,15,18,19,29,30,40,52,57,65,73,81,89,91]},{\"tag\":\"block\",\"leaf\":225,\"vertices\":[10,11,18,19,30,32,40,57,65,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":226,\"vertices\":[3,13,16,18,31,39,52,57,65,69,73,82,89,91]},{\"tag\":\"block\",\"leaf\":227,\"vertices\":[10,15,16,17,30,32,40,57,65,69,77,79,89,91]},{\"tag\":\"block\",\"leaf\":228,\"vertices\":[4,13,15,18,31,40,52,57,65,69,73,81,89,91]},{\"tag\":\"block\",\"leaf\":229,\"vertices\":[3,13,15,17,31,39,52,57,65,69,76,79,89,91]},{\"tag\":\"block\",\"leaf\":230,\"vertices\":[10,13,15,18,30,32,40,57,65,69,73,81,89,91]},{\"tag\":\"block\",\"leaf\":231,\"vertices\":[10,14,16,18,30,32,40,57,65,69,71,73,89,91]},{\"tag\":\"block\",\"leaf\":232,\"vertices\":[10,12,16,17,30,32,40,57,65,69,71,79,89,91]},{\"tag\":\"block\",\"leaf\":233,\"vertices\":[2,3,10,18,30,32,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":234,\"vertices\":[2,4,7,18,31,41,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":235,\"vertices\":[1,2,7,18,30,41,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":236,\"vertices\":[2,4,7,17,31,41,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":237,\"vertices\":[4,7,10,18,31,40,57,65,69,71,73,81,89,91]},{\"tag\":\"block\",\"leaf\":238,\"vertices\":[3,7,10,17,31,39,57,65,69,71,76,79,89,91]},{\"tag\":\"block\",\"leaf\":239,\"vertices\":[4,10,11,18,27,32,40,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":240,\"vertices\":[10,14,16,17,27,32,40,44,57,65,71,89,90,91]},{\"tag\":\"block\",\"leaf\":241,\"vertices\":[10,14,16,18,27,32,40,44,57,65,71,88,89,91]},{\"tag\":\"block\",\"leaf\":242,\"vertices\":[0,2,3,17,29,44,52,57,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":243,\"vertices\":[0,2,10,18,32,38,44,57,65,77,81,88,89,91]},{\"tag\":\"block\",\"leaf\":244,\"vertices\":[2,12,13,18,31,38,44,52,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":245,\"vertices\":[2,3,10,18,27,32,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":246,\"vertices\":[2,7,12,18,31,41,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":247,\"vertices\":[1,2,7,18,27,41,44,57,65,71,81,88,89,91]},{\"tag\":\"block\",\"leaf\":248,\"vertices\":[2,7,13,17,31,41,44,57,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":249,\"vertices\":[10,13,15,18,27,32,40,44,57,65,81,88,89,91]},{\"tag\":\"block\",\"leaf\":250,\"vertices\":[2,3,13,17,31,44,52,57,65,76,82,89,90,91]},{\"tag\":\"block\",\"leaf\":251,\"vertices\":[2,13,14,17,31,38,44,52,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":252,\"vertices\":[3,13,15,17,31,37,44,52,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":253,\"vertices\":[13,14,15,17,31,40,44,52,57,65,76,89,90,91]},{\"tag\":\"block\",\"leaf\":254,\"vertices\":[2,7,14,17,31,41,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":255,\"vertices\":[7,10,14,17,31,40,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":256,\"vertices\":[3,7,10,17,31,37,44,57,65,71,76,89,90,91]},{\"tag\":\"block\",\"leaf\":257,\"vertices\":[4,10,11,16,27,32,40,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":258,\"vertices\":[2,3,11,16,29,30,52,57,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":259,\"vertices\":[2,7,11,16,29,30,41,57,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":260,\"vertices\":[11,14,15,16,29,30,40,52,57,65,73,89,90,91]},{\"tag\":\"block\",\"leaf\":261,\"vertices\":[3,10,11,16,27,32,39,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":262,\"vertices\":[10,11,14,16,30,32,40,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":263,\"vertices\":[3,10,11,16,30,32,37,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":264,\"vertices\":[2,3,11,13,31,45,52,57,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":265,\"vertices\":[2,7,11,13,31,41,45,57,65,73,82,89,90,91]},{\"tag\":\"block\",\"leaf\":266,\"vertices\":[11,13,14,15,31,40,45,52,57,65,73,89,90,91]},{\"tag\":\"block\",\"leaf\":267,\"vertices\":[2,7,11,14,31,41,45,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":268,\"vertices\":[2,7,11,12,31,41,45,57,65,71,79,88,89,91]},{\"tag\":\"block\",\"leaf\":269,\"vertices\":[7,10,11,14,31,40,45,57,65,71,73,89,90,91]},{\"tag\":\"block\",\"leaf\":270,\"vertices\":[10,13,14,15,31,40,45,56,58,65,73,85,87,90]},{\"tag\":\"block\",\"leaf\":271,\"vertices\":[10,13,14,15,31,40,44,53,58,65,76,85,87,90]},{\"tag\":\"block\",\"leaf\":272,\"vertices\":[2,3,10,13,31,45,56,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":273,\"vertices\":[2,3,10,13,31,44,53,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":274,\"vertices\":[4,13,15,16,31,37,41,56,58,65,73,85,87,90]},{\"tag\":\"block\",\"leaf\":275,\"vertices\":[2,13,14,15,31,41,45,56,58,65,73,85,87,90]},{\"tag\":\"block\",\"leaf\":276,\"vertices\":[8,13,15,18,27,32,40,44,57,66,81,85,87,88]},{\"tag\":\"block\",\"leaf\":277,\"vertices\":[2,13,14,15,31,41,44,53,58,65,76,85,87,90]},{\"tag\":\"block\",\"leaf\":278,\"vertices\":[11,13,15,19,31,39,41,53,58,65,76,79,85,87]},{\"tag\":\"block\",\"leaf\":279,\"vertices\":[8,13,15,18,30,32,40,57,66,69,73,81,85,87]},{\"tag\":\"block\",\"leaf\":280,\"vertices\":[2,13,18,19,31,41,45,56,58,65,73,82,85,87]},{\"tag\":\"block\",\"leaf\":281,\"vertices\":[2,13,18,19,31,41,44,53,58,65,76,82,85,87]},{\"tag\":\"block\",\"leaf\":282,\"vertices\":[1,2,11,18,25,41,45,58,65,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":283,\"vertices\":[1,2,11,18,30,41,53,58,65,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":284,\"vertices\":[2,5,13,17,31,41,44,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":285,\"vertices\":[0,2,8,18,32,38,44,57,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":286,\"vertices\":[1,2,11,17,25,41,45,58,65,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":287,\"vertices\":[2,4,11,17,25,29,41,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":288,\"vertices\":[2,12,13,17,31,41,45,56,58,65,82,85,87,90]},{\"tag\":\"block\",\"leaf\":289,\"vertices\":[0,2,3,18,32,45,57,64,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":290,\"vertices\":[1,2,11,16,30,41,53,58,65,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":291,\"vertices\":[2,4,11,13,31,41,53,58,65,76,82,85,87,90]},{\"tag\":\"block\",\"leaf\":292,\"vertices\":[2,12,13,16,31,41,44,53,58,65,82,85,87,90]},{\"tag\":\"block\",\"leaf\":293,\"vertices\":[0,2,3,16,32,44,57,62,66,77,82,85,87,88]},{\"tag\":\"block\",\"leaf\":294,\"vertices\":[0,2,3,15,32,44,57,62,66,77,81,85,87,88]},{\"tag\":\"block\",\"leaf\":295,\"vertices\":[2,5,11,13,31,41,45,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":296,\"vertices\":[2,5,11,16,29,30,41,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":297,\"vertices\":[2,4,13,16,31,41,56,58,65,73,82,85,87,90]},{\"tag\":\"block\",\"leaf\":298,\"vertices\":[0,2,3,15,32,45,57,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":299,\"vertices\":[0,2,4,16,32,38,57,64,66,77,79,85,87,88]},{\"tag\":\"block\",\"leaf\":300,\"vertices\":[3,11,16,17,30,32,35,57,66,77,82,85,87,90]},{\"tag\":\"block\",\"leaf\":301,\"vertices\":[11,17,18,19,30,32,35,38,57,66,77,81,85,87]},{\"tag\":\"block\",\"leaf\":302,\"vertices\":[11,14,16,17,30,32,35,38,57,66,77,85,87,90]},{\"tag\":\"block\",\"leaf\":303,\"vertices\":[11,15,17,19,30,32,40,57,62,66,77,81,85,87]},{\"tag\":\"block\",\"leaf\":304,\"vertices\":[11,14,15,17,30,32,40,57,62,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":305,\"vertices\":[2,3,11,17,30,32,57,62,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":306,\"vertices\":[2,3,17,18,30,32,57,64,66,77,82,83,85,87]},{\"tag\":\"block\",\"leaf\":307,\"vertices\":[2,14,17,18,30,32,38,57,64,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":308,\"vertices\":[3,15,17,18,30,32,37,57,64,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":309,\"vertices\":[14,15,17,18,30,32,40,57,64,66,77,83,85,87]},{\"tag\":\"block\",\"leaf\":310,\"vertices\":[15,16,17,19,30,32,40,57,64,66,77,79,85,87]},{\"tag\":\"block\",\"leaf\":311,\"vertices\":[2,16,17,19,30,32,38,57,64,66,77,79,85,87]},{\"tag\":\"block\",\"leaf\":312,\"vertices\":[8,15,17,18,30,32,40,57,66,69,77,81,85,87]},{\"tag\":\"block\",\"leaf\":313,\"vertices\":[8,15,16,17,30,32,40,57,66,69,77,79,85,87]},{\"tag\":\"block\",\"leaf\":314,\"vertices\":[3,16,17,18,30,32,35,57,66,69,77,82,85,87]},{\"tag\":\"block\",\"leaf\":315,\"vertices\":[3,15,17,18,30,32,35,57,66,69,77,81,85,87]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[6,9,50,57,58,65,66,85,86,89,91]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[7,10,32,41,52,58,66,72,86,87,89,91]}]}"
  "1016 -154 0 524 519 0\n1017 173 0 628 622 0\n1018 183 0 628 626 0\n1019 170 0 1017 587 0\n1020 180 0 1018 617 0\n1021 201 0 674 675 672 673 668 669 671 637 634 635 632 639 287 310 286 312 289 311 309 1015 0\n1022 -210 0 1021 697 695 0\n1023 -208 0 1022 691 0\n1024 -204 0 1022 694 0\n1025 -206 0 1023 686 0\n1026 -197 195 0 1025 653 652 684 660 662 397 403 665 0\n1027 -205 0 1023 688 652 653 655 656 658 405 407 410 1026 666 667 681 396 402 659 0\n1028 -197 0 1027 682 0\n1029 -196 0 1027 683 0\n1030 -60 0 1028 666 0\n1031 -68 0 1028 667 0\n1032 -55 0 1029 660 0\n1033 -61 0 1029 661 0\n1034 -62 0 1029 662 0\n1035 -64 0 1029 663 0\n1036 -69 0 1029 664 0\n1037 -29 0 1032 1030 395 0\n1038 -47 0 1033 404 0\n1039 -37 0 1034 1031 401 0\n1040 -56 0 1035 409 0\n1041 -48 0 1036 406 0\n1042 200 -207 0 1022 1027 1040 1039 1041 1038 1037 685 693 679 644 678 648 672 673 670 671 636 640 638 391 385 651 0\n1043 198 0 668 669 633 635 630 631 632 305 408 279 280 307 277 304 306 1014 0\n1044 194 34 -209 0 1043 697 696 676 672 670 642 641 1042 689 649 650 677 393 399 643 0\n1045 43 -209 0 1043 697 1024 696 676 1042 687 654 672 670 642 641 640 389 1044 680 645 646 394 400 647 0\n1046 -43 44 25 0 1024 390 648 644 680 0\n1047 -209 0 697 1043 696 676 672 1042 670 687 640 654 1045 1046 0\n1048 -207 0 1047 690 0\n1049 -203 0 1047 692 0\n1050 -195 0 1048 687 0\n1051 -194 0 1049 678 0\n1052 -193 0 1049 679 0\n1053 -44 0 1050 654 0\n1054 -52 0 1050 657 0\n1055 -43 0 1051 648 0\n1056 -76 0 1051 649 0\n1057 -81 0 1051 650 0\n1058 -34 0 1052 644 0\n1059 -75 0 1052 645 0\n1060 -79 0 1052 646 0\n1061 -25 0 1053 1055 1058 388 0\n1062 -27 0 1059 1056 392 0\n1063 -35 0 1060 1057 398 0\n1064 -39 -163 0 46 59 79 102 552 0\n1065 -54 -33 80 41 38 -164 -162 -161 -159 0 14 13 55 56 63 124 175 535 137 543 24 39 548 557 158 0\n1066 -63 82 -165 0 86 184 561 0\n1067 -70 82 -165 0 108 186 561 0\n1068 -46 80 41 38 -164 -162 0 47 48 160 548 15 122 557 0\n1069 -45 41 38 -162 0 40 41 548 0\n1070 166 72 0 1017 628 582 583 580 623 573 616 620 595 606 609 599 601 1064 540 151 153 155 156 1066 1067 1068 552 55 124 1069 557 158 189 548 561 83 0\n1071 -84 -177 -83 57 0 595 593 153 151 158 163 180 548 543 24 0\n1072 -74 -177 -83 57 0 595 593 153 151 122 129 178 548 543 24 0\n1073 -177 -83 57 54 26 -181 0 156 155 153 151 607 593 595 1069 1071 1072 557 597 599 1066 1067 604 552 44 47 127 548 543 82 190 561 0\n1074 -83 57 54 26 -184 0 618 612 151 153 155 156 1073 614 606 609 599 601 1066 1067 552 44 48 127 160 1068 557 592 178 543 0\n1075 177 83 167 72 0 628 586 624 616 614 623 606 585 1064 580 540 573 0\n1076 -36 45 84 -164 26 0 122 139 557 0\n1077 -40 -165 0 83 145 183 561 0\n1078 38 41 84 -179 -162 26 0 601 1077 599 1069 548 1076 0\n1079 -38 -163 54 0 45 78 101 552 0\n1080 -88 -78 -1 -33 -11 -10 -16 -65 -80 -89 -46 -58 -41 0 412 698 0\n1081 157 92 160 169 -65 -80 -89 -46 -58 26 -41 0 1035 1017 1037 1062 1061 1054 1040 413 311 29 387 541 247 92 44 43 42 67 37 28 27 26 530 567 273 244 584 578 576 569 531 14 195 535 1080 287 340 700 0\n1082 -88 -32 78 -8 158 -89 -80 -65 -46 -58 -41 0 1036 1035 1040 1033 1017 42 334 92 43 153 32 412 358 341 172 810 540 528 573 567 576 584 0\n1083 78 -8 158 -159 -89 -80 -65 -46 -58 -41 0 1054 1017 1040 1033 1035 1036 534 92 43 42 67 29 387 153 32 334 535 1082 312 528 273 244 567 584 576 573 540 339 357 876 0\n1084 158 -159 33 -89 -80 -65 -46 -58 26 -41 0 1041 1056 1017 92 44 29 387 153 32 28 534 272 1083 135 224 337 211 540 573 576 584 567 528 307 312 812 0\n1085 -78 -53 33 -89 -80 -65 -46 -58 -41 0 1056 29 387 114 247 92 96 273 311 288 44 65 28 224 211 714 0\n1086 -159 33 -89 -80 -65 -46 -58 -41 0 1033 1041 1038 92 43 42 65 29 387 37 28 1084 531 96 114 288 311 273 247 1085 334 535 335 874 0\n1087 -53 159 66 -41 0 1017 153 32 96 114 528 540 567 569 584 578 0\n1088 33 -89 -80 -65 -46 -58 -41 0 1019 1017 92 153 37 32 28 1086 571 1087 531 575 576 569 584 540 567 172 528 307 0\n1089 -67 78 -89 -80 -65 -46 -58 -41 0 1061 1062 1037 1036 1035 1040 1033 42 334 44 27 26 65 1088 195 43 29 387 153 32 307 312 358 341 815 0\n1090 159 -89 -80 -65 -46 -58 -41 0 1061 1062 1037 1054 1017 1040 1033 1035 1036 42 44 27 26 65 1088 195 53 92 67 153 32 539 334 1089 528 273 244 567 584 578 569 540 339 357 717 0\n1091 -89 -80 -65 -46 -58 -41 0 1037 1062 1061 629 1041 553 562 560 602 610 92 44 43 42 526 68 65 29 387 551 153 37 32 27 26 547 1088 596 14 53 532 195 621 625 1090 572 535 579 135 337 589 540 568 573 1081 308 313 414 715 0\n1092 -78 -33 -80 -65 -46 -58 -41 0 1056 1061 1062 1037 1041 42 44 27 26 65 195 127 70 1091 543 593 143 266 185 359 92 29 387 153 32 135 337 1075 567 528 307 312 820 0\n1093 -33 -80 -65 -46 -58 -41 0 1056 628 1037 1062 1061 524 1060 1035 1036 127 44 70 1091 543 593 616 623 588 578 143 266 432 185 359 434 492 498 500 43 42 65 29 387 153 37 32 27 26 14 53 195 415 436 445 467 520 515 1092 325 535 427 569 480 540 485 357 475 313 425 0\n1094 159 33 -171 66 -41 0 37 28 571 1087 576 531 0\n1095 158 -174 66 -41 0 588 153 32 577 576 585 573 567 540 528 172 307 0\n1096 -80 -65 -46 -58 -41 0 628 92 127 44 70 153 37 28 1091 543 593 616 623 1093 1095 531 96 114 528 1075 567 0\n1097 -53 -65 -46 -58 -41 0 628 1096 92 160 127 48 44 70 65 153 32 96 114 528 540 567 573 1075 580 593 585 543 623 178 620 557 609 599 0\n1098 -185 80 -46 -58 0 160 127 48 44 70 65 616 620 593 609 543 599 178 557 0\n1099 72 -89 -65 -46 -58 -41 0 1057 628 1061 1062 1037 42 44 27 26 65 37 28 1097 92 1096 1098 623 1095 531 195 14 588 578 298 146 240 43 29 387 153 32 247 540 573 569 580 535 585 567 528 307 312 828 0\n1100 -89 -65 -46 -58 -41 0 1057 628 1062 524 1059 1037 1061 1035 1036 1096 298 433 493 495 499 42 44 27 26 65 37 28 1097 92 1098 623 1095 531 195 415 436 445 467 520 517 146 240 429 477 127 29 387 178 1099 321 357 427 313 481 425 486 475 0\n1101 -65 -46 -58 -41 0 1057 628 1037 1062 1061 524 1036 1035 1054 146 44 42 67 65 29 387 153 37 32 28 27 26 92 185 1096 240 298 429 433 477 479 482 1097 1098 623 1095 531 195 415 436 445 467 520 512 1100 359 434 494 496 500 503 515 490 485 430 475 358 425 312 244 0\n1102 11 53 89 -46 -58 -41 0 628 1054 1034 1063 1058 1036 1035 1037 1062 1061 1030 524 127 44 70 543 593 616 623 588 578 1101 252 426 474 484 80 43 42 69 67 65 29 387 27 384 153 37 32 30 28 26 244 313 303 312 292 357 1095 358 423 540 531 430 454 569 14 195 490 456 535 415 460 333 436 432 445 497 468 502 521 511 0\n1103 66 -139 53 -174 -46 -58 -41 0 1031 1037 1062 1061 524 1035 1036 513 522 1101 80 44 42 68 65 29 387 37 28 27 26 236 1095 423 531 454 195 456 415 460 436 445 469 468 461 521 457 514 455 501 424 490 308 430 357 247 0\n1104 16 -33 -66 -11 177 -46 -58 -41 0 1061 1062 1037 1041 1040 1033 1035 628 1036 42 44 27 26 65 195 14 70 1101 252 160 146 48 43 29 387 153 32 31 337 247 535 339 357 571 580 590 624 614 609 599 601 561 187 356 808 557 0\n1105 -33 53 89 -46 -58 -41 0 628 1037 1062 1061 524 1030 1041 1038 127 44 70 543 593 616 623 1101 252 426 1102 425 476 487 1103 43 42 69 65 27 26 195 415 436 445 467 520 515 1104 430 490 501 502 517 497 488 432 479 333 478 335 428 0\n1106 53 89 -46 -58 -41 0 628 1040 1033 1035 1036 127 44 70 543 593 616 623 588 1101 252 426 160 146 48 43 42 65 153 37 32 31 29 28 1102 425 476 487 1103 1105 531 272 577 576 590 571 573 624 540 614 135 339 357 609 535 599 601 561 187 356 967 557 0\n1107 89 -46 -58 -41 0 628 1036 1037 70 1101 252 160 146 127 48 44 43 42 65 29 387 153 32 31 27 543 593 616 623 588 578 1106 96 114 288 311 247 540 1075 573 569 567 580 528 590 624 614 609 599 601 561 187 356 557 136 322 535 964 0\n1108 78 -53 -46 -58 -41 0 628 1033 1041 1038 1107 178 48 65 160 1101 146 190 561 32 153 114 540 573 580 590 624 618 607 597 557 96 601 609 620 623 585 567 528 588 578 569 29 387 247 311 288 70 252 43 42 334 535 335 806 0\n1109 -53 -46 -58 -41 0 628 1056 1101 146 1107 190 561 601 609 620 623 178 70 252 160 48 44 65 29 387 153 32 28 53 96 114 288 311 247 540 573 580 590 585 624 567 618 528 607 597 557 1108 224 211 804 0\n1110 -92 -78 -66 -46 -58 -41 0 1041 1056 628 1107 178 48 65 160 1101 146 190 561 32 153 135 540 573 580 590 624 618 607 597 557 37 28 1109 601 609 620 623 588 576 531 44 211 337 29 303 70 252 414 805 0\n1111 88 -78 -66 -46 -58 -41 0 1041 1056 628 1054 1040 1110 413 1107 178 48 65 160 1101 146 190 561 32 153 135 540 573 580 590 624 618 607 597 557 37 28 1109 601 609 620 623 588 576 531 44 211 337 29 303 70 252 287 340 756 0\n1112 -78 -66 -46 -58 -41 0 1041 1056 628 1109 37 29 303 1101 146 1107 190 561 601 609 620 623 588 178 70 252 160 48 44 65 153 32 28 135 337 211 540 573 580 576 590 531 624 618 607 597 557 1111 412 748 0\n1113 129 53 31 28 -58 0 1040 1054 1033 1030 74 67 465 467 460 445 458 436 422 415 218 206 0\n1114 1 -46 -58 -41 0 1030 1037 1062 1061 1054 1056 628 1040 1033 1035 1036 1109 1101 146 1107 190 561 601 609 620 623 588 178 70 252 160 127 48 44 42 74 67 65 153 37 32 29 28 27 26 206 195 218 208 531 577 1095 576 590 303 573 624 540 618 339 357 607 809 597 557 0\n1115 -32 -1 30 -41 0 1037 1062 1061 29 28 27 26 7 14 191 0\n1116 158 -46 -58 -41 0 628 43 1114 1115 1101 146 1107 190 561 601 609 620 623 588 42 1095 576 1112 571 535 0\n1117 -66 -46 -58 -41 0 1040 1033 1035 1036 628 37 28 1109 1116 531 43 1114 1115 1101 146 1107 190 561 601 609 620 623 588 578 178 70 252 160 48 42 65 153 32 29 303 1112 334 535 571 569 580 540 590 339 357 624 807 618 557 607 597 0\n1118 -46 -58 -41 0 628 1031 1035 1054 1060 1059 1041 70 67 29 387 153 37 32 28 80 146 1101 252 426 474 1107 178 190 561 601 609 620 623 1109 1114 1116 531 1117 236 1103 487 485 476 479 480 425 477 427 244 429 325 307 312 348 337 835 0\n1119 -80 -89 -1 -78 66 -33 -58 -41 0 1041 1053 1037 1062 628 190 177 4 32 153 135 540 573 580 590 624 618 337 137 1118 69 29 387 141 142 149 349 232 552 604 606 601 620 561 623 585 567 528 307 312 837 0\n1120 -65 80 84 70 -181 74 46 54 26 0 84 86 557 552 599 604 0\n1121 179 -67 -82 -165 -89 -1 -78 -33 -58 -41 0 1041 628 1053 1037 1062 29 387 312 307 177 4 32 153 135 540 573 580 590 624 618 337 1118 70 69 604 602 552 558 294 831 232 0\n1122 -174 -165 -89 -1 -78 66 -33 -58 -41 0 1041 628 629 1053 1031 190 65 69 1118 136 32 153 135 540 573 580 590 624 618 177 180 1119 1120 561 551 547 596 337 29 387 625 585 621 567 528 307 312 1121 599 610 557 555 380 236 824 0\n1123 -88 -45 -10 -11 -63 -82 -89 -1 -78 -33 -58 -41 0 1041 153 32 337 412 699 0\n1124 90 -45 -10 -11 -63 -82 -89 -1 -78 -33 -58 -41 0 1041 1054 1040 1123 153 32 337 287 340 701 0\n1125 -165 -89 -1 -78 66 -33 -58 -41 0 1041 628 1035 1054 65 69 1118 136 32 153 135 540 573 580 590 624 618 177 180 1119 1120 190 532 539 572 579 337 53 526 67 561 1122 623 589 620 568 606 609 530 552 599 244 273 557 1124 413 709 0\n1126 -89 -1 -78 66 -33 -58 -41 0 1041 1039 1060 1055 1057 628 32 153 135 540 573 580 590 624 618 607 337 136 1118 69 65 29 387 177 180 1119 1125 563 601 597 327 240 609 604 557 620 552 623 585 567 528 307 312 832 0\n1127 -63 -67 89 -1 -78 -33 -58 -41 0 1041 628 1030 29 387 312 307 32 153 135 540 573 580 590 624 137 4 70 543 593 614 609 601 599 69 333 337 136 65 107 142 1066 165 362 557 821 0\n1128 -1 -78 66 -33 -58 -41 0 628 32 153 135 540 573 580 590 624 137 136 1118 70 69 65 4 1126 543 593 1075 614 567 606 609 528 599 601 1127 552 103 161 1067 557 149 0\n1129 -82 -164 45 74 26 0 149 165 557 0\n1130 63 66 -33 -15 -41 -84 82 1 -78 -58 0 1063 1033 1030 1041 1032 628 135 153 32 540 573 580 590 624 618 337 29 387 189 161 69 133 131 206 174 333 65 201 379 552 604 606 601 620 561 623 585 567 528 307 312 1007 0\n1131 -63 -33 -15 -41 -84 1 -78 -58 0 1039 1038 1041 1033 1030 1016 1062 1035 1054 53 429 477 479 69 133 131 206 174 333 432 497 32 153 337 430 490 502 518 488 29 387 200 70 67 294 426 476 425 244 307 312 1002 0\n1132 -33 -15 -41 -84 82 1 -78 -58 0 1063 628 135 153 32 540 573 580 590 624 618 189 161 133 65 201 69 1131 552 1130 604 92 601 561 0\n1133 -41 -84 80 82 1 -78 -58 0 1054 1039 1038 1033 1030 1057 1041 1061 524 1032 1062 1053 161 69 133 131 206 174 333 432 497 200 132 66 383 70 64 28 29 32 153 240 337 429 430 477 490 479 502 482 511 521 1132 194 416 435 445 467 468 520 460 515 456 458 485 453 422 474 424 285 426 273 295 0\n1134 181 41 -84 40 72 57 0 1018 628 158 618 613 624 595 1071 590 548 580 22 573 540 0\n1135 163 169 33 -181 91 82 0 628 580 606 604 620 601 623 561 588 585 92 576 567 528 94 96 307 531 169 0\n1136 169 33 -181 41 91 70 36 82 40 46 54 0 628 580 590 624 1135 1079 552 548 1066 595 601 614 609 0\n1137 -67 -158 33 0 94 96 307 531 169 0\n1138 -66 -181 91 70 82 46 54 0 91 92 552 561 604 601 0\n1139 167 41 36 40 72 -58 0 628 70 69 65 586 624 1074 1075 595 548 22 1079 540 606 573 620 580 623 585 0\n1140 -184 -67 40 163 32 72 41 -84 82 -58 0 1034 1032 628 1060 1063 307 411 169 189 70 1134 604 601 561 94 93 606 620 623 588 578 555 379 69 372 180 163 158 64 382 65 1074 614 593 595 543 548 6 17 22 343 226 540 573 569 1135 535 1006 0\n1141 83 -3 38 -31 -78 -160 -33 -65 -67 -19 72 -84 -58 0 1034 1041 1037 307 411 69 372 540 351 1005 0\n1142 -78 -160 -33 177 -65 -67 -19 1 72 41 -84 -58 0 1034 1056 1041 1053 307 411 169 93 387 94 69 372 158 65 211 544 596 549 230 1141 249 1004 0\n1143 40 163 32 1 72 41 -84 82 -157 -58 0 1032 1018 628 606 611 555 379 189 180 163 161 160 158 70 69 1134 1138 604 528 601 561 1140 624 619 590 577 580 1137 571 573 13 1142 535 6 16 543 548 592 0\n1144 163 32 1 72 41 -84 82 -157 -58 0 1018 180 163 70 1143 24 1077 543 601 593 604 613 0\n1145 32 1 72 41 -84 82 -157 -58 0 1034 1062 1038 1055 1033 1030 1041 1053 1036 1054 628 69 372 161 160 159 158 70 65 1144 1064 1079 552 75 76 91 1066 294 199 206 528 601 548 230 307 609 595 169 411 614 246 624 590 577 580 1137 571 573 535 540 1003 0\n1146 -32 72 -84 82 -157 -58 0 1018 628 189 180 163 161 160 70 69 65 12 14 543 593 613 616 1138 623 528 588 1137 577 576 590 573 624 1074 614 540 606 1064 0\n1147 -163 -67 -1 32 72 41 -84 82 -58 0 1034 1036 1054 1062 1018 628 307 411 169 163 180 70 4 543 593 69 372 161 160 159 158 1064 1079 552 246 75 76 1066 294 601 609 611 614 592 624 548 590 577 580 1137 571 573 535 540 823 0\n1148 72 41 -84 82 -157 -58 0 1018 628 189 180 163 161 160 158 70 69 1146 1145 4 543 593 613 1138 528 1147 606 604 611 614 601 592 624 1077 590 548 580 22 151 573 540 0\n1149 -72 -84 82 -157 -58 0 1018 628 189 180 163 161 160 70 69 110 135 172 307 528 1138 618 613 624 593 590 543 580 6 12 571 535 0\n1150 -31 -141 -41 -84 82 -58 0 1057 1034 1033 1030 1016 1031 69 372 432 497 502 518 164 240 429 477 163 161 4 6 1133 330 427 481 483 486 516 474 503 426 498 250 493 298 433 0\n1151 -84 82 -157 -58 0 1054 1057 1060 1039 1058 628 66 383 64 382 70 69 160 161 163 164 180 1149 1148 32 153 240 540 342 573 430 580 490 590 624 1150 543 593 614 606 609 552 601 1066 0\n1152 -182 70 46 82 54 0 606 609 552 601 1066 0\n1153 -157 -164 -158 80 66 30 28 -168 -41 82 -58 0 1040 1033 1038 1039 153 32 65 1151 528 182 1137 339 14 540 569 535 136 1128 557 200 0\n1154 -63 -178 -174 -41 82 -58 0 588 578 153 37 32 28 75 76 91 142 1066 1095 597 1153 567 585 580 571 573 540 114 135 531 535 14 0\n1155 157 -181 -161 70 -41 82 -58 0 628 1040 1033 1036 1035 1054 1031 1030 69 1118 1152 620 623 607 1154 552 604 601 153 37 32 28 70 67 65 529 530 567 1095 273 585 580 571 573 540 110 114 135 339 357 531 244 14 535 6 121 125 543 180 190 363 561 1120 254 877 0\n1156 -28 -66 -72 84 -165 -41 82 -58 0 1033 1040 1035 1036 1060 1018 628 153 31 92 561 356 190 187 29 387 114 37 357 313 339 69 1118 1067 1152 1066 552 28 70 65 6 121 125 324 331 543 593 613 614 604 624 599 590 557 577 938 531 0\n1157 33 28 -91 -66 -72 84 182 163 -41 -58 0 1040 1035 1036 628 1033 153 31 356 190 187 29 387 114 37 357 313 339 135 110 620 623 588 28 70 69 65 272 531 577 576 590 571 624 535 618 614 12 604 593 599 543 129 332 953 557 0\n1158 74 -164 -161 -33 28 -91 -66 -72 84 -41 -58 0 1033 1040 1035 1036 1055 1038 1039 14 153 31 356 190 187 29 387 114 37 357 313 339 70 69 65 373 557 39 200 786 543 0\n1159 -72 -157 -165 -41 82 -58 0 1040 1033 1035 1036 628 1038 1039 1034 1055 1063 1151 69 1118 1067 1152 1066 552 29 387 153 37 31 70 110 114 135 172 339 357 307 313 528 92 561 190 356 1156 1157 14 535 571 580 590 624 618 614 604 593 599 1158 123 129 326 263 543 960 0\n1160 -78 -91 -164 -161 84 -58 0 190 187 70 65 136 137 557 543 39 0\n1161 32 -77 -45 -18 78 -91 -66 28 -158 -159 -16 -41 -58 0 1036 1038 1039 153 31 356 37 28 535 200 13 531 288 311 784 0\n1162 74 -91 -66 28 -164 -161 -158 -159 72 84 -41 -58 0 1036 1055 1160 153 31 356 190 187 29 387 247 37 28 70 69 65 373 557 39 543 1161 14 221 531 288 311 951 0\n1163 -66 28 -164 72 84 70 -41 82 -58 0 628 1036 1038 1039 1034 1055 1063 69 1118 1152 153 32 540 573 580 590 624 614 593 618 620 623 588 576 578 569 29 387 247 37 31 28 70 92 1138 190 356 1160 1162 123 129 326 263 543 12 535 13 531 288 311 958 0\n1164 28 -157 -165 -41 82 -58 0 628 1039 1060 1055 1033 1030 1059 1040 1061 1032 1067 69 1118 1066 552 153 32 1159 540 573 580 590 624 618 604 599 1152 620 623 588 576 578 569 29 387 247 1151 1163 528 307 312 1137 13 14 1153 535 143 187 1128 327 561 206 174 368 378 1008 0\n1165 -157 -165 -41 82 -58 0 628 1059 1060 1030 69 1118 1067 1152 1066 552 29 387 153 32 64 382 70 65 1151 1159 540 247 573 580 590 624 618 614 593 1164 6 121 125 319 324 543 190 1138 561 1135 528 1120 254 307 312 814 0\n1166 -165 -41 82 -58 0 628 1118 69 1067 1152 1165 567 586 624 618 614 1155 593 0\n1167 157 -41 182 70 82 -58 0 628 567 586 624 618 614 1155 593 0\n1168 -181 -41 46 70 82 -58 0 628 1166 601 69 1152 620 623 607 604 1154 552 0\n1169 80 -164 -89 -28 -66 -33 -72 84 -41 82 -58 0 1033 1040 1036 1035 1060 1057 1053 324 121 91 29 387 114 37 357 313 339 65 240 380 557 939 0\n1170 -41 70 82 -58 0 1018 628 1040 1033 1035 1036 1060 1020 1063 1032 1062 1053 70 69 28 29 32 33 37 153 1118 1166 1168 387 1152 618 613 1167 624 593 1151 590 577 580 571 573 540 110 114 135 172 339 357 531 307 313 14 528 535 91 6 125 324 552 543 603 597 1169 141 197 295 955 0\n1171 -11 -12 -80 -17 -72 41 -58 0 1033 1036 1035 524 1039 1063 1058 1040 1054 1038 1055 1056 426 143 140 139 431 489 501 172 307 119 386 357 339 114 111 109 66 383 74 67 65 64 425 243 476 418 487 439 514 440 521 443 470 467 468 444 446 520 460 442 436 515 456 458 417 415 502 453 422 225 497 424 272 218 199 432 273 959 266 0\n1172 -66 -2 -28 -42 -80 -17 -72 41 82 -58 0 1033 1040 1036 1035 1032 1062 1053 1018 125 99 42 6 74 283 187 141 140 139 357 339 70 69 1138 295 613 593 595 543 548 803 0\n1173 -28 11 -80 -17 -72 41 82 -58 0 1036 1035 1062 628 172 307 282 119 114 357 313 164 142 140 386 109 69 65 64 42 99 193 1152 552 1172 528 567 586 624 618 614 604 595 1078 0\n1174 46 70 -184 -80 41 82 -58 0 618 164 142 140 69 65 1152 552 614 604 595 1078 0\n1175 -46 -128 -80 -147 78 41 0 1062 1060 524 143 139 234 325 417 427 441 480 443 482 469 510 522 0\n1176 66 28 -42 -80 -147 -72 41 82 -58 0 1033 1040 1036 1035 1062 1060 628 74 283 422 143 140 139 172 307 357 339 135 110 70 68 528 308 567 424 586 453 624 459 461 1175 1174 177 1067 296 371 601 609 620 614 623 593 595 585 548 580 24 571 543 535 861 0\n1177 -42 172 -66 -72 -77 -40 -70 -80 -58 0 1060 1033 1040 1036 1035 541 357 339 143 371 74 65 35 283 533 581 574 538 223 210 773 0\n1178 42 -148 -118 -72 31 28 41 -58 0 1054 1036 1035 524 1037 1062 1061 119 386 357 114 66 383 65 64 248 313 418 425 439 475 440 484 511 521 470 468 446 460 436 458 415 422 195 272 0\n1179 -42 -72 -184 -70 -80 41 82 -58 0 1060 629 177 1067 601 609 614 593 70 140 139 595 548 24 543 627 143 371 432 497 499 99 526 1176 1177 529 591 568 0\n1180 -32 -77 -40 -11 -4 -66 -72 -70 -80 -58 0 1060 1033 1036 1035 1040 1054 357 339 114 143 371 74 67 218 936 0\n1181 -40 42 -66 -72 -70 -80 41 -58 0 1060 628 1033 1040 1036 1035 1056 248 418 439 440 443 119 114 357 313 339 135 109 149 1067 601 609 620 623 588 143 371 432 497 100 99 164 65 24 1178 502 489 431 257 1180 535 210 571 775 576 531 0\n1182 42 -66 -72 -70 -80 41 -58 0 628 135 114 109 149 1067 601 609 100 99 140 139 1181 548 595 614 624 590 577 580 531 571 14 535 0\n1183 40 -66 -72 -70 -80 41 -58 0 1060 1018 1033 1040 1035 628 1036 1031 1055 1039 1063 99 100 135 149 1182 1179 624 590 580 571 535 12 74 283 357 339 1067 601 609 611 143 371 177 104 141 140 139 70 548 238 198 592 934 543 0\n1184 -66 -72 -70 -80 41 -58 0 1060 1033 1040 1036 1035 628 1059 1061 1041 1037 357 339 135 560 600 556 608 143 371 104 100 99 149 74 1182 283 1179 624 619 590 580 571 535 1183 550 596 546 321 349 771 0\n1185 -72 -70 -80 41 -58 0 1060 628 149 1067 601 609 620 623 143 371 432 497 499 100 99 109 114 135 172 307 1184 528 1176 567 585 577 580 531 571 14 535 0\n1186 42 -66 -32 -14 -77 -40 -158 -16 -70 -80 -58 0 1054 1060 1058 14 9 8 143 371 102 66 383 64 228 531 288 311 927 0\n1187 -92 -42 -66 -32 -14 -77 -40 -16 -70 -80 -58 0 1060 74 283 143 371 414 770 0\n1188 86 -42 -66 -32 -14 -77 -40 -16 -70 -80 -58 0 1060 1034 1035 1187 74 283 143 371 66 306 374 753 0\n1189 -70 -80 41 -58 0 1054 1060 1039 628 1061 155 149 143 140 139 66 383 64 382 74 70 99 100 102 177 1067 371 601 609 620 623 588 578 1185 540 346 573 569 580 576 590 585 624 567 614 593 595 548 24 543 137 323 535 14 1137 528 1186 283 1188 411 745 0\n1190 -184 182 -80 41 -58 0 1189 149 140 139 614 1174 595 47 548 0\n1191 77 -53 -14 -32 -40 -161 -39 -12 -66 -80 -58 0 1041 1037 1056 311 288 24 46 143 70 543 349 208 800 0\n1192 -32 -40 -39 -158 -66 72 70 -80 -58 0 1053 1062 1032 1018 1033 1031 69 149 187 46 1138 613 593 117 36 19 70 141 295 14 221 531 288 311 1191 332 361 764 0\n1193 -53 -89 -78 32 -40 -39 -12 -66 -80 -58 0 1030 1055 1060 1039 1033 1040 46 164 149 327 24 20 206 21 288 311 219 798 0\n1194 -92 -11 -33 -89 -1 -78 -40 -39 -12 -66 -80 -58 0 1055 1060 1039 46 164 149 327 414 799 0\n1195 -86 -11 -33 -89 -1 -78 -40 -39 -12 -66 -80 -58 0 1055 1060 1039 46 164 149 327 411 749 0\n1196 -66 72 -80 41 -58 0 1032 1062 1053 628 1018 1033 1030 1039 1060 1055 1034 1035 1189 187 164 155 149 141 140 139 70 69 66 92 295 561 601 609 1190 624 590 577 580 571 573 540 19 20 21 36 46 117 1138 386 613 593 595 548 24 1192 535 206 137 327 543 1193 531 303 1194 1195 306 374 757 0\n1197 -40 72 -80 41 -58 0 1036 628 1018 1033 1030 1039 1060 1055 1196 1189 164 155 149 142 140 70 69 65 24 47 550 251 235 1174 552 1078 624 604 586 590 613 567 577 580 593 528 571 573 307 1137 540 411 13 14 20 535 206 137 327 543 836 0\n1198 31 -78 -65 -3 -39 -161 77 -33 32 -67 -80 -58 0 1033 1030 1041 1053 1037 1062 46 349 20 307 411 141 70 206 543 229 997 0\n1199 -39 -161 77 -33 32 72 -80 41 -58 0 1018 1063 1041 1037 628 1056 13 1196 139 1197 1139 567 528 307 411 93 140 548 595 613 1189 187 164 149 143 64 20 46 1064 227 1174 349 604 624 601 590 561 580 571 535 1198 174 315 266 1009 0\n1200 -161 77 -33 32 72 -80 41 -58 0 1036 1054 1039 1058 628 1063 13 140 139 1197 548 595 616 623 588 578 1196 1139 567 528 307 411 169 93 1189 187 155 149 66 383 70 65 64 1199 540 346 246 573 569 225 580 590 624 614 1174 609 42 44 201 601 535 543 996 561 0\n1201 176 72 83 0 1018 628 611 612 606 624 1064 590 540 580 573 0\n1202 -33 32 72 -80 41 -58 0 628 140 139 1197 548 155 1201 592 1189 149 13 1200 125 127 137 1174 535 624 571 590 580 0\n1203 158 72 -80 41 -58 0 628 140 139 1197 548 595 616 623 588 1189 155 149 577 576 590 573 624 540 1174 46 0\n1204 72 -80 41 -58 0 139 1196 1197 1139 567 528 1203 1137 14 1202 0\n1205 167 -174 32 -80 41 -58 0 628 1204 135 110 1189 149 586 585 624 580 1174 571 42 535 0\n1206 177 32 -80 41 -58 0 1018 628 1204 172 307 135 110 1189 187 149 69 613 616 623 1205 567 528 92 1138 561 42 601 535 609 571 1190 580 624 590 0\n1207 -33 -80 41 -58 0 1030 628 1060 1204 172 307 135 110 1189 164 149 140 139 70 14 282 1206 595 548 47 251 1174 1171 624 324 590 535 580 571 0\n1208 -28 11 -80 41 -58 0 1060 1204 164 149 324 1173 0\n1209 32 28 -80 41 -58 0 628 1204 135 110 1189 149 140 139 1206 535 595 571 548 580 47 590 1174 624 0\n1210 77 -17 -40 -161 -12 -66 -32 28 -42 -8 -72 -80 -58 0 1033 1040 1036 1035 1059 1037 1061 12 357 339 143 70 321 543 802 0\n1211 -77 -40 -66 -32 -42 -8 -72 70 -80 -58 0 1040 1036 1035 1053 1062 1032 1033 1031 70 141 295 357 339 187 69 332 361 765 0\n1212 -177 -66 -42 -80 41 -58 0 1054 1035 1036 1053 1062 1032 1056 70 141 1189 295 1204 111 67 109 34 243 1208 1209 119 386 114 1207 272 164 140 139 593 595 548 1211 257 1210 0\n1213 -66 -42 -80 41 -58 0 1033 1040 1054 1035 1036 1032 1053 1018 1062 1060 1204 111 67 109 34 243 1208 1209 12 119 386 114 1207 272 357 339 135 1189 187 149 143 141 140 139 70 69 92 295 561 601 609 611 1212 613 1138 47 127 234 325 548 966 592 543 0\n1214 -42 -80 41 -58 0 1033 1040 1036 1035 1054 628 1056 1062 1060 1204 119 386 114 1207 272 172 307 357 339 135 111 109 1189 187 149 143 139 68 67 34 243 1208 1209 1213 308 528 1176 567 499 586 497 624 432 1174 1190 266 234 325 871 609 561 601 0\n1215 -80 41 -58 0 628 1062 1060 524 139 143 149 1189 1204 109 114 119 135 172 386 307 1207 272 422 458 460 1214 281 248 531 425 418 577 475 439 590 624 1174 234 325 417 427 442 480 444 485 471 513 522 0\n1216 -139 74 -4 -127 24 36 -58 0 1054 524 1033 1034 1055 1056 1039 1063 1058 418 439 440 443 468 521 66 383 69 64 513 514 522 499 501 471 495 497 489 444 493 432 431 442 433 332 372 373 417 353 257 225 0\n1217 3 74 158 -8 -72 36 70 41 -58 0 1054 1040 1030 1036 1035 1060 1058 1038 1039 1033 1059 1037 1061 1056 628 1034 1055 1063 135 119 114 357 533 313 425 475 386 422 458 460 248 1216 485 480 427 325 70 487 476 426 251 577 590 624 618 172 307 339 110 1215 66 383 69 65 64 225 241 16 1079 1152 329 334 321 604 620 1120 266 601 623 263 561 588 585 576 567 571 528 535 954 0\n1218 74 158 33 -72 36 70 41 -58 0 1036 1035 524 1062 1033 1056 119 386 114 272 422 458 460 357 533 313 425 475 484 509 523 473 248 418 439 135 109 64 1216 485 480 427 1217 417 442 444 447 471 435 522 416 510 193 499 334 497 266 432 0\n1219 -3 89 77 120 -115 -184 33 -72 36 41 -58 0 1054 1061 612 119 386 110 109 66 383 70 69 64 23 417 442 447 435 416 194 543 593 592 614 548 606 1079 0\n1220 158 33 -72 36 70 41 -58 0 1036 1035 524 1062 628 119 386 114 272 422 458 460 357 135 110 70 69 533 577 248 313 590 418 425 624 439 475 484 509 523 473 1218 121 129 178 1219 234 241 1152 620 614 623 593 588 543 576 12 571 535 0\n1221 -175 -176 33 40 -74 -72 36 41 -58 0 1033 1040 1036 1035 1018 1055 1063 1032 1062 1053 1038 1039 119 386 114 272 178 129 123 121 172 307 357 339 135 110 109 70 69 586 590 567 577 580 528 531 571 535 12 543 593 592 613 548 45 101 144 198 1138 295 326 797 0\n1222 182 33 40 -74 -72 36 41 -58 0 1054 1033 1040 1036 1035 1018 628 1061 1038 1039 1056 119 386 114 272 178 129 123 121 172 307 357 339 135 110 109 66 383 70 69 64 620 611 623 1221 624 618 614 593 595 543 548 12 44 194 101 144 535 1220 326 571 531 580 1136 585 317 801 567 528 0\n1223 -31 -174 -165 -163 33 -3 -74 -72 80 -58 0 1054 1033 1040 1036 1035 1061 1059 588 119 386 114 272 121 172 307 357 339 135 110 109 66 383 69 64 12 44 194 535 571 580 576 585 531 567 528 91 552 1067 377 933 0\n1224 -70 -32 -42 -66 31 -165 -8 -3 -74 -72 80 -58 0 1033 1040 1036 1035 1059 23 357 339 1067 377 255 932 0\n1225 33 -3 -74 -72 41 -58 0 1033 1040 1036 1035 628 1032 1062 1053 1059 23 178 129 123 122 121 172 307 119 386 357 339 154 135 114 110 109 1215 70 69 272 1222 606 609 1079 601 548 595 616 623 1223 543 592 612 624 586 590 567 577 580 528 531 571 91 92 535 1224 552 295 146 348 561 965 0\n1226 161 -184 40 36 41 54 0 612 593 592 614 548 606 1079 0\n1227 -72 -165 -163 -31 -3 -74 41 -58 0 628 1040 1033 1035 1036 1041 1038 1059 23 122 69 1079 548 595 616 623 1064 44 12 136 121 1215 110 172 339 357 1225 535 307 282 213 571 580 585 567 528 91 552 1067 377 931 0\n1228 -30 -163 46 54 0 76 100 552 0\n1229 -163 -31 -3 -74 41 -58 0 628 44 12 23 136 122 121 70 69 65 1064 1079 548 595 616 623 588 578 1228 535 571 569 580 590 624 1074 614 540 609 1227 601 0\n1230 -74 41 159 163 -31 -58 0 628 1039 1040 1033 1035 1036 1041 1038 1032 1062 1053 606 571 580 590 624 614 595 70 65 69 1074 618 620 623 585 567 588 578 569 556 44 39 24 122 548 22 144 540 326 172 339 357 1222 307 282 213 528 295 1138 961 0\n1231 41 159 163 -31 -58 0 628 571 580 590 624 618 604 599 606 620 623 585 567 39 65 1215 1230 557 1129 1151 0\n1232 159 163 -31 -58 0 628 1030 1040 1033 1035 1036 1031 606 620 623 588 578 556 555 174 39 70 69 65 571 569 580 576 590 585 624 567 618 1074 604 599 601 1231 28 29 32 37 1166 387 540 147 362 354 1129 114 172 339 357 250 531 307 313 528 923 0\n1233 -41 -78 163 45 -58 0 628 136 135 556 65 32 153 1170 540 1129 573 599 580 604 590 618 624 0\n1234 -82 -78 163 -31 -58 0 1030 1036 1031 1018 628 1054 1040 39 1233 174 69 333 136 135 556 555 24 65 144 147 156 362 354 1129 250 599 604 618 613 624 595 586 590 548 567 577 580 88 573 528 540 167 182 307 1137 999 340 0\n1235 -39 -158 -157 -17 -162 -165 82 41 -78 70 -31 -58 0 1030 1060 1032 1215 174 69 333 24 64 382 70 22 117 344 548 82 88 293 561 528 307 1137 312 1000 0\n1236 164 -78 163 -31 -58 0 1020 1030 1018 628 1057 1032 1054 1040 1041 1038 1234 39 1233 174 69 333 135 603 556 24 70 597 599 604 618 613 1134 624 595 256 586 590 567 577 580 573 1235 540 151 548 82 88 293 561 528 167 182 307 1137 340 213 998 0\n1237 -78 163 -31 -58 0 39 24 65 135 136 1233 1215 1234 1236 557 158 1151 1139 567 0\n1238 -36 -164 45 26 0 158 1076 0\n1239 42 -91 -12 -83 -66 -158 -17 -74 -3 -30 -31 -58 0 115 13 3 531 249 288 311 956 0\n1240 -86 -42 -91 -12 -83 -66 -17 -74 -3 -30 -31 -58 0 74 283 411 907 0\n1241 -90 -42 -91 -12 -83 -66 -17 -74 -3 -30 -31 -58 0 74 283 413 957 0\n1242 -164 82 41 163 -31 -58 0 1041 1018 1057 628 1062 1053 1032 1040 1215 1232 12 6 1237 535 110 21 17 13 606 556 44 39 24 74 70 69 66 65 1238 1139 548 230 567 595 1151 613 614 557 256 624 590 577 580 1137 573 528 540 295 1138 1239 283 1240 1241 367 279 915 0\n1243 181 41 -30 40 0 1018 628 17 13 618 613 624 595 586 590 548 567 577 88 1137 528 0\n1244 41 163 -31 -58 0 628 1232 12 6 1237 535 110 21 17 606 39 24 65 1243 604 599 1238 1242 548 156 595 540 614 573 624 580 590 0\n1245 163 -31 -58 0 1030 1036 1031 628 174 39 12 6 65 555 556 606 620 623 588 1232 1237 535 3 13 21 110 115 1244 37 153 1170 247 540 147 149 165 362 354 573 250 580 576 590 585 1137 531 624 567 528 288 311 618 922 604 557 599 0\n1246 33 -66 72 -179 -41 -31 -58 0 1054 1037 1019 1057 1038 44 69 1245 91 552 601 1166 149 188 299 1228 12 6 65 599 39 1129 136 535 1064 153 540 569 575 66 383 322 29 387 247 37 28 214 531 288 311 769 0\n1247 -90 67 72 -179 -41 -31 -58 0 1054 1037 1057 1017 69 44 1245 1228 12 6 65 599 39 601 1166 1129 136 535 1064 153 540 569 578 584 567 528 1246 282 91 552 149 188 299 66 383 322 29 387 247 413 928 0\n1248 86 67 72 -179 -41 -31 -58 0 1054 1037 1057 1017 1032 1040 1247 69 44 1245 1228 12 6 65 599 39 601 1166 1129 136 535 1064 153 540 569 578 584 567 528 1246 282 91 552 149 188 299 66 383 322 29 387 247 367 279 911 0\n1249 67 72 -179 -41 -31 -58 0 1054 1037 1017 1057 69 44 1245 1228 12 6 65 599 39 601 1166 1129 136 535 1064 153 540 569 578 584 567 66 383 322 29 387 247 188 149 528 91 299 552 1246 282 1248 411 903 0\n1250 -70 72 -179 -41 -31 -58 0 1054 1037 1019 1059 1062 29 387 1249 312 69 44 1245 1228 12 6 65 599 39 601 1166 1129 136 535 1064 153 540 569 575 1137 307 98 66 383 322 247 149 30 377 296 977 0\n1251 72 -179 -41 -31 -58 0 1054 1037 1019 1030 1031 69 44 1245 1228 12 6 65 599 39 601 1166 1129 136 535 147 29 387 153 1064 174 66 383 540 247 322 569 575 1249 307 1137 312 1250 552 362 250 818 0\n1252 70 -33 -179 -41 -31 -58 0 1033 1040 1036 1035 629 1030 1031 1251 172 307 526 544 551 596 1245 610 621 625 541 570 532 579 589 568 529 273 29 387 114 37 357 313 339 65 599 39 601 1166 1129 147 174 44 69 552 362 250 863 0\n1253 -33 -179 -41 -31 -58 0 629 1033 1040 1036 1035 1059 1062 1251 541 570 29 387 114 37 357 313 172 307 339 544 551 596 1245 610 621 625 65 599 39 601 1166 1129 149 30 526 532 579 589 568 529 273 1252 377 296 862 0\n1254 -179 -41 -31 -58 0 1040 1033 1035 1036 1038 1017 1057 29 387 37 28 69 44 1245 1228 39 12 6 65 599 601 1166 149 188 1129 136 535 571 1251 114 172 339 357 307 313 1253 214 531 272 576 584 567 528 91 299 552 778 0\n1255 -82 -66 -72 -41 -31 -58 0 1033 1040 1035 628 1036 1056 44 69 1245 91 552 114 37 28 1254 609 620 623 588 1228 12 6 135 535 571 576 531 29 387 357 313 339 174 563 354 602 559 207 266 919 0\n1256 74 -164 -66 -72 -41 -31 -58 0 1033 1040 1036 1035 628 1056 126 44 69 1245 91 552 1255 360 161 114 37 28 1254 609 620 623 588 1228 12 6 135 535 571 576 531 29 387 357 313 339 174 39 65 207 266 557 930 0\n1257 -72 -157 -178 -41 -31 -58 0 628 1040 1033 1035 1036 1059 1057 1254 609 620 623 588 29 387 37 28 69 44 1245 1228 126 12 6 114 135 172 339 357 535 307 313 571 528 576 91 531 552 1255 1067 360 597 1256 143 377 240 929 0\n1258 -164 -66 -90 -11 -70 -33 72 -41 -31 -58 0 628 1030 413 161 174 69 44 1245 1228 12 6 1254 609 620 623 588 578 1064 153 540 569 535 333 136 29 387 247 126 39 65 1129 557 360 925 0\n1259 -90 -11 -70 -33 -157 -178 -41 -31 -58 0 628 1030 1059 174 69 44 1245 1228 12 6 1254 609 620 623 588 578 1064 153 1257 540 569 535 333 29 387 247 182 413 528 1258 560 597 377 1166 921 0\n1260 86 -82 -19 -66 90 -11 -70 -33 72 -41 -31 -58 0 628 1030 1059 1040 1032 1061 174 69 44 1245 1228 12 6 1254 609 620 623 588 578 1064 153 540 569 535 333 29 387 247 64 382 66 365 279 916 0\n1261 164 -66 90 -11 -70 -33 72 -178 -41 -31 -58 0 628 1030 1059 174 69 44 1245 1228 12 6 1254 609 620 623 588 578 1064 153 540 569 535 333 29 387 247 560 597 377 1166 1260 411 908 0\n1262 -86 -66 -11 -70 -33 72 -41 -31 -58 0 1030 628 126 65 69 44 1245 1228 12 6 1254 609 620 623 588 578 1064 153 540 569 535 136 39 573 580 590 624 618 607 585 567 1259 1261 1129 360 161 557 174 333 29 387 247 411 909 0\n1263 -66 -11 -70 -33 72 -41 -31 -58 0 1030 628 1059 1040 1032 1061 1245 1064 153 540 573 580 590 624 618 607 1254 609 620 623 585 567 1259 161 174 69 44 1228 12 6 588 578 569 535 333 136 29 387 247 126 39 64 382 66 65 1261 1129 557 360 1262 365 279 917 0\n1264 149 -70 -110 -108 -31 0 1041 1037 1059 497 490 126 44 503 505 498 491 493 431 433 349 377 0\n1265 -41 129 -82 -70 -31 0 1040 1033 1041 1038 1031 100 12 467 445 435 416 215 219 105 465 462 451 420 202 460 456 454 423 108 107 29 214 236 303 1255 1263 0\n1266 129 -82 -70 -31 0 1033 1040 1031 1036 1054 105 102 101 24 465 467 460 462 443 456 458 451 440 441 453 422 420 439 417 424 202 418 74 217 1265 238 246 273 0\n1267 41 -157 -156 -158 -162 -82 -16 -18 -19 -70 -31 0 524 1030 1033 1054 1040 1041 1038 6 126 432 430 1264 1266 520 512 482 480 427 330 102 101 24 548 88 528 95 97 167 182 307 1137 525 340 1013 213 0\n1268 -67 66 -58 -41 17 -70 -31 0 1053 1037 1059 1056 1062 628 1040 1033 1036 1035 1254 609 620 623 1095 30 296 588 578 174 126 360 563 602 559 266 29 387 107 354 161 44 350 102 100 12 6 182 307 1137 312 339 358 540 1010 569 535 0\n1269 -169 83 -70 -31 0 102 100 12 6 571 573 535 540 135 0\n1270 66 -58 -41 17 -70 -31 0 1053 1037 1059 628 1254 609 620 623 161 126 44 350 1269 580 585 567 1268 528 0\n1271 -58 -41 17 -70 -31 0 1036 524 1053 1037 1059 628 1056 1033 1040 29 387 37 161 126 44 350 1269 580 360 1266 520 563 598 107 354 102 100 174 12 6 1254 609 602 620 559 623 266 588 432 578 585 567 1257 540 247 569 430 535 1264 512 484 475 425 1270 303 288 311 219 762 0\n1272 -78 51 -41 17 -70 -31 0 524 1053 1037 1059 1030 1041 628 1271 37 161 126 44 350 1269 580 360 1266 520 349 105 102 174 39 5 136 333 337 557 432 430 599 1264 609 512 620 484 623 475 585 425 566 284 525 0\n1273 -18 78 -66 -41 -82 -70 -31 0 524 1036 1033 1030 29 387 37 107 354 433 493 1266 520 126 6 432 330 498 427 500 480 515 482 485 512 475 1264 425 430 303 247 114 0\n1274 16 -66 -41 17 -70 -31 0 1053 1037 1059 1060 1040 1033 1036 1035 1054 1017 126 360 90 1272 1273 371 98 105 1271 202 29 387 37 28 161 44 350 1269 107 354 102 247 358 112 114 339 357 289 244 525 275 566 703 584 531 576 0\n1275 -66 -41 17 -70 -31 0 1036 1033 1041 1038 524 105 1271 202 420 37 107 126 360 354 433 493 495 1266 520 100 90 1272 1274 430 335 490 428 502 478 515 479 482 485 511 475 521 425 466 284 464 275 452 421 0\n1276 -16 152 -145 -70 -31 0 1030 1041 1038 508 105 100 174 430 490 1264 502 432 511 333 482 335 479 428 478 0\n1277 -41 17 -70 -31 0 1053 1037 1059 1017 1033 1062 524 1036 1035 161 126 44 350 1269 580 582 107 360 354 433 493 495 105 102 29 30 387 1271 202 420 451 1275 296 423 454 456 463 466 521 1276 247 358 113 312 289 528 525 565 0\n1278 -185 41 -70 26 0 161 101 616 620 595 609 1078 0\n1279 86 17 -70 -31 0 1041 628 1053 1037 1059 1036 1031 161 126 44 350 1269 580 5 1277 1278 623 585 567 566 590 624 349 556 101 39 24 280 307 528 88 90 238 548 525 1229 595 557 614 599 609 0\n1280 17 -70 -31 0 1059 1053 1041 1037 1036 628 1058 1030 161 107 105 102 100 174 126 44 39 12 6 5 360 350 349 354 1269 580 1277 590 624 1278 623 588 585 578 576 566 567 1279 168 171 172 540 347 569 535 136 333 557 1267 599 595 609 614 0\n1281 177 182 -70 -31 0 1018 628 161 100 39 12 6 5 613 614 607 624 590 580 571 1269 535 155 156 136 1067 557 597 0\n1282 -175 -36 41 -70 -31 0 1060 1054 1040 1041 1038 122 371 186 297 88 1280 102 100 12 6 586 590 566 567 577 580 528 571 1269 95 97 167 182 307 1137 535 525 340 1012 213 0\n1283 -162 41 -70 -31 0 1033 1060 628 1036 1035 5 1278 623 588 186 161 105 102 101 6 12 4 205 39 24 548 88 122 1076 297 371 1282 624 618 1074 607 1269 597 580 576 1067 585 566 567 528 1267 307 358 411 0\n1284 41 -70 -31 0 1033 628 556 105 102 100 544 594 6 12 4 205 39 5 1278 623 588 578 1283 595 1281 609 615 599 601 1074 1238 1067 1269 241 1129 580 136 1229 585 535 566 569 540 113 172 525 280 0\n1285 -33 72 -58 -66 67 -70 -31 0 1284 282 1263 0\n1286 -157 86 -156 -70 -31 0 628 1030 1038 1059 307 280 1284 153 1269 580 590 624 618 607 29 387 37 28 1280 161 105 102 100 174 39 12 6 5 528 90 525 1254 1257 609 540 247 620 623 588 578 576 569 535 136 333 1285 214 531 311 288 766 377 557 762 597 1067 0\n1287 86 -156 -70 -31 0 1017 628 1284 153 1269 580 102 100 39 12 6 5 280 1286 567 584 585 578 623 620 609 599 601 1254 1067 525 1129 113 136 540 535 569 0\n1288 58 -156 -70 -31 0 1033 1054 524 1280 431 1284 29 387 1287 172 247 430 491 504 170 37 28 105 100 12 202 525 420 220 284 451 416 425 462 435 475 445 484 468 511 521 0\n1289 -118 130 -149 59 -88 49 36 21 65 63 0 524 1034 1063 1058 467 468 520 460 512 456 458 484 454 422 475 423 290 425 292 282 0\n1290 11 -156 -70 -31 0 1040 1033 524 1030 628 1035 1054 1031 1059 100 12 6 102 1284 153 1287 172 540 1288 1254 609 620 623 588 578 569 535 28 29 387 107 108 26 30 27 384 411 74 247 430 174 105 333 432 1264 497 1276 521 1289 445 435 416 224 219 136 67 1269 580 590 624 618 607 37 1280 161 39 5 303 244 236 1011 377 557 1010 597 1067 0\n1291 -156 -70 -31 0 1054 628 1030 1031 524 1284 29 387 27 384 153 30 28 26 108 107 105 102 100 174 12 6 1287 172 411 540 247 430 1288 74 1254 609 620 623 588 578 569 535 333 432 497 1264 1276 521 1289 445 435 416 224 1290 425 1263 475 236 484 423 512 454 520 456 465 460 0\n1292 -70 -31 0 1017 628 1040 1033 1035 1036 39 12 6 5 100 102 105 107 1284 28 29 37 153 387 1269 580 582 1291 526 565 566 202 584 585 578 576 623 620 609 599 601 1067 354 1129 136 535 569 540 113 114 172 339 357 531 307 313 270 528 703 0\n1293 172 156 63 67 -31 0 1017 628 566 1292 44 39 5 582 585 565 623 528 620 92 606 609 552 599 601 124 1129 561 187 189 557 0\n1294 -169 30 -41 -31 0 153 32 12 6 571 573 535 540 135 0\n1295 -91 -164 74 -31 0 39 5 187 189 557 0\n1296 84 -65 -164 -54 -78 -51 -33 -41 -11 -31 0 1057 1060 136 1295 5 39 1129 29 387 113 247 305 278 557 256 370 892 0\n1297 63 -33 86 -41 -11 58 -31 0 1017 628 1032 1041 1037 13 1294 580 307 280 29 387 153 32 31 1292 44 39 12 6 5 1293 525 90 113 278 305 528 540 247 567 584 585 578 623 569 620 535 606 609 136 552 599 601 1129 1295 561 1296 379 351 893 0\n1298 -33 86 -41 -11 58 -31 0 1017 628 307 280 153 32 1292 44 39 12 6 5 13 1294 580 582 1297 81 91 528 567 565 584 585 525 578 623 113 620 540 609 1152 569 599 1129 535 136 0\n1299 -172 33 -41 0 153 37 32 28 577 580 531 573 114 540 0\n1300 156 172 67 -31 0 1017 582 565 1293 528 91 0\n1301 86 -41 -11 58 -31 0 1017 153 37 32 28 280 307 1298 1299 1300 525 54 90 113 531 528 540 567 573 584 576 0\n1302 -59 33 169 42 23 -31 0 1017 628 1292 44 39 5 73 97 531 576 588 584 623 567 620 528 606 609 91 92 552 599 601 124 1295 1129 561 0\n1303 33 169 51 42 23 58 -31 0 1017 580 1302 525 566 1300 584 1137 576 0\n1304 84 -54 -65 -164 -78 -67 -7 -33 -86 -41 -31 0 1057 1060 5 136 39 1129 1295 29 387 172 247 411 557 256 370 720 0\n1305 -41 -11 58 -31 0 1017 628 1032 1041 1037 1292 44 39 12 6 5 28 29 31 32 37 153 387 1301 170 172 411 540 247 573 580 1303 13 72 270 525 566 1300 584 585 578 623 569 620 535 609 136 599 601 1295 1129 1066 561 1152 1304 379 351 721 0\n1306 -185 41 -31 0 39 24 5 616 620 595 606 609 599 1238 548 58 1079 0\n1307 -182 -179 -67 -7 167 -33 41 -31 0 1033 1040 628 1041 1038 1031 1057 601 13 12 6 1306 623 585 580 571 535 136 599 1295 5 39 1129 561 1066 1238 182 339 116 312 307 1292 44 24 606 621 1152 1064 1075 213 155 355 242 557 887 0\n1308 -179 -67 -7 167 -33 41 -31 0 628 1033 1040 182 339 1306 623 585 580 573 586 624 6 12 4 205 39 24 5 599 1238 1307 610 614 554 595 1074 548 540 22 0\n1309 -67 -7 167 -33 41 -31 0 628 1040 1033 1041 1038 1057 1032 13 12 6 1306 623 585 580 571 535 573 586 624 618 607 116 1292 4 205 544 24 5 182 307 312 339 1308 609 604 614 1064 595 213 540 151 155 156 1073 1071 548 1065 256 82 293 889 597 561 0\n1310 179 -66 -184 41 -31 0 91 88 618 1292 44 24 609 604 614 552 595 58 548 0\n1311 -66 74 -184 41 -31 0 39 5 92 1310 599 601 1295 1129 561 0\n1312 156 -33 41 58 -31 0 628 13 1306 623 583 12 6 566 586 624 585 580 571 535 136 565 1311 528 276 1309 0\n1313 182 -179 -51 41 -31 0 1033 628 5 39 599 1238 1306 623 90 95 528 567 585 580 573 586 624 113 6 12 4 205 24 610 614 554 595 1074 548 540 22 0\n1314 -179 -51 -33 41 -11 -31 0 628 1041 1038 1057 1031 13 12 6 1306 623 90 95 528 567 585 580 571 535 136 305 278 113 1292 44 39 24 5 599 601 1238 1295 1129 1066 561 1313 606 621 1152 1064 1075 213 155 242 355 557 899 0\n1315 -33 -11 58 -31 0 1033 628 1041 1038 1057 1032 1305 1306 623 1292 6 12 4 205 544 24 5 13 72 1312 525 90 95 113 278 305 528 567 586 585 624 580 618 571 573 607 535 1314 609 604 614 1064 595 213 540 151 155 156 1073 1071 548 1065 256 82 293 901 597 561 0\n1316 -51 -36 -54 33 -174 -31 0 1032 1033 1061 628 1059 1037 1053 1292 6 12 4 205 293 5 158 39 1076 88 82 59 57 126 44 49 50 51 52 54 95 113 278 305 271 194 528 567 586 585 624 577 580 618 531 571 573 607 535 540 597 156 350 738 561 0\n1317 -36 -54 -156 -11 58 -31 0 1032 1040 1033 1054 628 1059 1037 1053 59 57 1315 1305 1306 623 1292 6 12 4 205 126 44 39 5 82 88 158 1076 293 1316 525 73 97 181 280 274 528 339 169 411 567 220 586 585 624 577 580 618 531 571 573 607 535 540 597 156 350 726 561 0\n1318 -54 182 -156 -11 58 -31 0 1033 1041 628 1062 524 1059 1037 1053 1032 1315 1305 425 1292 6 12 4 205 126 44 39 24 57 58 59 81 1317 548 230 595 417 614 441 624 586 590 567 577 580 1137 571 573 528 535 90 295 135 525 426 540 71 280 476 387 169 487 224 416 435 446 470 521 514 499 501 495 489 493 431 433 350 379 0\n1319 -83 67 36 54 179 41 -31 0 1033 628 1018 1292 6 12 4 205 44 24 5 151 1074 548 624 595 586 613 567 604 528 552 91 0\n1320 -172 83 23 72 53 33 0 577 580 531 573 36 540 0\n1321 -59 36 54 179 33 41 -31 0 1040 1033 628 1306 623 73 97 181 280 339 169 1319 1320 590 585 624 567 1310 528 0\n1322 36 179 -156 -11 58 -31 0 628 609 1318 1315 1305 1306 623 1321 525 51 54 90 95 113 528 1319 567 1320 585 0\n1323 179 -156 -11 58 -31 0 628 1315 1292 44 609 1318 1322 77 88 552 604 618 624 586 590 567 577 528 1137 0\n1324 -67 -156 58 0 95 97 525 0\n1325 -51 54 67 -179 41 -31 0 1033 1306 544 594 6 12 4 205 5 90 113 1313 528 615 621 567 1074 1075 0\n1326 167 23 72 53 54 33 -174 -31 0 1033 628 6 12 4 205 5 586 585 624 1320 1074 0\n1327 -184 -66 72 54 -179 41 -31 0 1033 628 44 1292 91 552 606 1306 623 588 578 6 12 4 205 5 1311 1074 614 136 162 595 1078 17 22 535 540 569 0\n1328 54 -156 -11 58 -31 0 1040 1033 1032 1062 1053 628 1057 1030 1324 5 39 1323 599 1238 601 1315 1305 1306 623 1292 6 12 4 205 126 44 24 202 1325 525 73 181 280 339 169 411 1326 567 528 92 295 1327 624 590 577 580 1320 531 571 156 242 561 364 1295 136 994 535 0\n1329 90 -84 -19 -83 -78 -158 66 -65 -3 -54 -156 33 58 -31 0 1054 1040 278 288 525 71 166 280 274 387 340 169 224 531 885 0\n1330 -156 -11 58 -31 0 628 1041 1053 1031 1061 1315 1305 1306 623 544 594 39 12 6 5 1323 599 601 1238 1324 1328 57 58 81 124 1318 230 1295 1129 615 621 561 1311 528 567 585 577 580 571 535 130 134 135 381 1075 155 355 557 1329 181 413 525 51 52 54 271 531 194 897 0\n1331 -11 58 -31 0 628 12 6 1305 1306 623 583 1315 1330 566 565 586 585 624 577 580 1137 571 528 1310 1311 124 136 1327 535 110 0\n1332 -72 58 -31 0 12 6 110 113 135 172 535 280 307 571 525 1300 580 0\n1333 159 156 83 58 -31 0 1017 566 584 578 1332 571 569 580 576 540 1300 32 1137 276 1309 0\n1334 -30 167 83 54 72 46 0 628 21 1228 540 606 573 620 580 623 585 0\n1335 -182 74 54 -31 0 1292 44 39 5 609 1152 599 1129 0\n1336 156 -184 54 58 -31 0 1033 628 6 12 4 205 5 1074 1332 1070 44 566 565 1333 1334 535 136 1335 620 623 585 577 580 1294 1312 1311 1137 528 0\n1337 42 -156 11 58 0 284 302 525 0\n1338 -184 54 58 -31 0 1033 628 1332 1331 6 12 4 205 5 1074 1336 1324 1337 36 37 540 573 580 1306 623 585 567 528 1310 1327 0\n1339 54 58 -31 0 1033 628 1032 1062 1053 1057 1030 1332 1331 1292 6 12 4 205 126 44 39 24 202 1338 624 586 590 566 567 580 1324 1337 528 571 573 36 37 118 88 90 92 295 540 525 156 242 1319 280 289 599 601 561 364 1295 994 136 535 0\n1340 -26 2 30 22 23 24 33 0 1037 192 0\n1341 -28 2 33 21 23 24 0 1062 193 0\n1342 1 31 26 21 22 28 -33 0 1061 1062 1037 195 0\n1343 -26 5 40 46 0 1039 1038 196 0\n1344 5 46 40 45 -32 0 1063 1039 1055 198 0\n1345 1 32 -45 28 0 1039 1038 200 0\n1346 -32 6 54 57 58 0 1030 203 0\n1347 -57 1 32 28 0 1033 205 0\n1348 1 31 -58 28 32 0 1030 1033 206 0\n1349 -32 13 77 74 0 1056 208 0\n1350 1 -78 26 31 0 1056 211 0\n1351 4 -32 42 39 41 0 1041 212 0\n1352 4 -33 41 39 0 1038 1041 213 0\n1353 2 -41 32 33 30 0 1038 214 0\n1354 2 -42 32 30 0 1038 1041 215 0\n1355 2 -8 23 30 32 50 0 1054 1040 1033 216 0\n1356 8 -32 50 53 59 0 1054 1040 218 0\n1357 2 -53 32 30 0 1040 1033 219 0\n1358 2 23 32 -59 30 0 1054 1033 220 0\n1359 3 36 -39 21 24 40 0 1063 227 0\n1360 4 -40 42 21 22 23 24 39 0 1058 228 0\n1361 5 46 31 45 -3 0 1062 1037 1053 1041 229 0\n1362 3 36 38 41 -31 0 1053 1041 230 0\n1363 -36 31 5 46 0 1037 1041 231 0\n1364 5 31 45 -41 46 0 1062 1037 1053 232 0\n1365 -45 3 41 38 0 1037 1041 233 0\n1366 3 -46 36 41 0 1062 234 0\n1367 9 65 -41 63 66 0 1031 236 0\n1368 3 -65 41 38 0 1036 237 0\n1369 3 -66 40 38 41 0 1031 1036 238 0\n1370 15 80 -41 82 0 1057 240 0\n1371 3 -83 36 40 0 1057 242 0\n1372 -53 4 41 39 0 1035 1036 245 0\n1373 4 -67 39 23 41 0 1054 1036 246 0\n1374 12 -40 57 70 0 1030 251 0\n1375 -57 5 40 46 0 1031 253 0\n1376 5 -65 46 31 0 1030 254 0\n1377 -40 17 77 84 0 1056 257 0\n1378 5 -82 45 31 0 1056 259 0\n1379 -26 12 65 70 0 1034 260 0\n1380 -45 6 54 58 0 1034 261 0\n1381 12 65 -54 45 0 1063 262 0\n1382 12 65 45 70 -58 0 1063 1055 1034 263 0\n1383 18 74 -58 89 0 1056 266 0\n1384 9 65 36 -67 21 49 63 0 1058 1063 1034 292 0\n1385 12 -36 57 70 0 1032 293 0\n1386 -63 12 45 57 0 1062 294 0\n1387 12 -66 70 45 57 0 1053 1062 1032 295 0\n1388 9 66 36 -70 0 1062 296 0\n1389 19 91 -66 80 0 1057 299 0\n1390 -57 20 84 91 0 1057 314 0\n1391 45 -89 12 65 0 1057 316 0\n1392 -91 12 45 57 0 1056 317 0\n1393 -13 14 22 30 71 72 0 1061 1037 1059 318 0\n1394 -28 14 71 72 0 1059 319 0\n1395 13 74 -30 71 77 0 1059 320 0\n1396 13 74 77 28 -72 0 1061 1037 1059 321 0\n1397 14 30 72 22 -74 0 1037 322 0\n1398 14 -77 72 22 71 30 0 1061 323 0\n1399 -28 82 17 84 0 1060 324 0\n1400 13 -46 78 74 0 1060 325 0\n1401 17 -74 82 46 0 1039 1038 326 0\n1402 17 84 -78 82 46 0 1055 1060 1039 327 0\n1403 13 78 74 28 -82 0 1055 1038 328 0\n1404 -84 13 78 28 0 1039 1038 329 0\n1405 13 -18 77 28 78 0 1030 1033 330 0\n1406 -77 18 54 0 1033 332 0\n1407 18 -78 54 89 0 1030 333 0\n1408 -89 28 78 13 0 1033 334 0\n1409 14 -16 30 78 0 1038 1041 335 0\n1410 14 78 30 -83 0 1038 338 0\n1411 -72 90 0 1033 1040 339 0\n1412 88 85 90 -78 0 1040 1054 340 0\n1413 -15 16 22 39 71 72 0 1058 1039 1060 342 0\n1414 16 -38 71 72 0 1060 343 0\n1415 15 82 80 71 -39 0 1060 344 0\n1416 15 80 -72 82 38 0 1058 1039 1060 345 0\n1417 16 -80 39 22 72 0 1039 346 0\n1418 16 -82 39 22 71 72 0 1058 347 0\n1419 15 -46 80 83 0 1059 348 0\n1420 17 84 46 77 -83 0 1053 1037 1059 350 0\n1421 15 -84 83 38 0 1037 1041 351 0\n1422 15 -19 83 82 38 0 1031 1036 352 0\n1423 19 -82 63 0 1036 354 0\n1424 19 91 63 -83 0 1031 355 0\n1425 15 -91 38 83 0 1036 356 0\n1426 -72 92 0 1036 1035 357 0\n1427 16 -88 83 39 0 1035 1036 358 0\n1428 20 91 70 -77 0 1031 361 0\n1429 20 -82 70 89 0 1030 362 0\n1430 17 -91 77 46 0 1030 364 0\n1431 85 86 49 71 -18 90 0 1061 1032 1040 1059 365 0\n1432 86 85 71 -54 90 0 1059 366 0\n1433 85 86 49 90 -74 0 1040 1032 367 0\n1434 18 -86 74 89 54 0 1061 1040 1032 1059 368 0\n1435 85 86 49 71 -89 90 0 1061 1040 369 0\n1436 20 91 -54 84 0 1060 370 0\n1437 18 74 -70 0 1060 371 0\n1438 -84 18 54 0 1034 372 0\n1439 18 -91 74 54 0 1055 373 0\n1440 19 91 80 63 -86 0 1058 1035 1060 1034 375 0\n1441 19 91 -92 49 71 63 80 0 1058 1034 1060 376 0\n1442 19 80 -70 0 1059 377 0\n1443 19 -84 63 0 1032 379 0\n1444 -89 63 80 19 0 1053 380 0\n1445 -22 49 0 1054 383 0\n1446 -49 22 0 1054 384 0\n1447 -139 -149 0 1016 516 0\n1448 -140 -148 0 1016 518 0\n1449 -129 -153 0 524 520 0\n1450 -130 -152 0 524 521 0\n1451 -131 -151 0 524 522 0\n1452 -132 -150 0 524 523 0\n1453 158 168 0 1019 575 0\n1454 166 172 0 1017 582 0\n1455 167 171 0 1017 584 0\n1456 163 178 0 1020 603 0\n1457 176 182 0 1018 611 0\n1458 177 181 0 1018 613 0\n1459 174 185 0 628 623 0\n1460 175 184 0 628 624 0\n1461 -175 -184 0 629 627 0\n1462 -164 -59 -83 -78 -66 -42 -54 -31 0 118 289 280 155 37 58 24 1369 6 12 4 1347 39 1292 1387 57 1354 124 81 5 1295 557 1440 981 0\n1463 -175 -156 58 -31 0 1339 57 12 1331 1337 1354 118 37 1324 59 58 1332 1292 6 4 1347 126 44 39 24 586 590 567 580 528 571 573 88 90 92 1387 1369 535 540 548 525 156 595 280 289 1458 607 1462 597 561 1430 988 0\n1464 164 -59 -83 -78 -184 -42 -54 -31 0 118 289 37 124 1311 274 280 156 618 607 57 12 1354 58 1292 6 4 1347 126 44 24 599 597 609 614 595 1071 548 1420 82 1385 561 726 0\n1465 -59 -156 58 -31 0 1332 1339 59 1331 1337 37 1306 1459 1324 124 1463 1460 1311 528 567 585 580 573 540 156 155 57 12 6 571 535 533 282 81 58 4 1347 39 5 181 280 1464 1238 1295 557 1362 1440 1071 1329 614 561 609 601 0\n1466 -156 58 -31 0 1339 124 81 59 58 57 1332 1331 39 24 12 6 5 1324 1337 282 37 1354 1306 1459 1463 1460 1311 528 567 585 580 571 573 535 540 130 134 155 156 1446 1465 525 283 278 305 1316 548 1362 595 614 609 599 601 1295 557 561 1441 897 0\n1467 -42 58 -31 0 1466 566 586 1460 1332 1070 565 1339 124 37 94 1311 528 0\n1468 41 58 -31 0 1466 566 586 1460 1332 1070 565 1339 124 1306 1312 1311 1459 528 585 1137 577 0\n1469 58 -31 0 39 12 6 5 1331 1332 1339 57 58 81 124 1466 566 1467 302 1468 28 29 153 1294 387 1333 580 1303 247 535 1300 585 270 307 312 1459 620 609 599 601 1129 1295 561 1304 1443 1421 721 0\n1470 -41 -31 0 6 12 4 1347 39 44 1469 69 1292 1245 552 1386 91 1228 1064 66 1445 64 382 174 29 153 1170 1294 1254 387 563 1429 580 609 598 602 620 559 1459 1383 588 585 1095 578 567 528 1257 307 1137 312 540 1418 569 1001 535 0\n1471 -31 0 4 5 6 12 24 39 44 174 1347 1292 1469 69 1245 1064 552 1228 1079 77 91 142 1386 1470 548 1362 595 1229 1458 1383 1335 607 614 1460 586 590 567 577 580 528 571 573 167 182 307 1137 535 1412 1411 1352 540 1003 156 557 1066 597 0\n1472 -63 -12 -89 -162 -78 -83 -33 -67 41 -58 0 1471 65 1350 137 530 156 1151 93 387 94 307 169 249 151 411 77 80 548 1420 830 0\n1473 165 164 -78 -83 -33 -67 41 -58 0 1471 558 65 1350 137 93 387 94 307 169 249 151 411 1215 70 69 562 597 607 1456 1458 593 595 543 177 1391 1472 1444 552 47 826 548 0\n1474 -89 -165 -78 -83 -33 -67 74 41 -58 0 1471 156 1066 1067 1077 65 1350 530 1151 93 387 94 307 169 249 151 411 1215 69 190 1444 561 82 1368 548 987 595 1120 1458 0\n1475 164 -78 -83 -33 -67 74 41 -58 0 1471 65 1350 137 93 387 94 307 169 249 156 151 411 70 69 599 609 1457 1473 1077 1067 1066 1474 543 1383 593 592 1458 548 604 82 552 561 822 1385 0\n1476 -78 -83 -33 -67 74 41 -58 0 1471 530 156 1151 93 387 94 307 169 249 151 411 1215 70 69 65 137 1350 1475 557 48 103 1365 1069 258 1152 595 1457 1458 592 543 1474 991 601 552 604 0\n1477 -148 -136 70 -115 -83 57 0 482 440 443 467 1449 511 515 1450 485 470 474 444 426 442 1385 1374 417 1371 0\n1478 -83 -159 -33 -67 74 41 -58 0 14 13 307 169 93 387 530 94 70 69 156 249 1151 418 439 1476 1410 535 428 75 99 1399 478 431 479 489 1477 502 495 497 493 432 433 1439 1424 0\n1479 145 63 -86 74 80 54 0 495 497 493 432 433 1439 1440 0\n1480 -136 139 -148 -113 -39 24 -58 0 102 70 64 482 485 511 474 1450 426 470 1385 1374 446 1359 441 417 0\n1481 -3 -82 117 -89 -19 -78 -39 -33 -67 -58 0 1471 147 14 20 1348 79 46 307 411 66 64 417 442 438 419 1361 1363 983 1384 0\n1482 -148 -89 -19 -78 -39 83 -33 -67 41 -58 0 1471 14 20 1348 415 436 96 1113 1449 22 307 411 93 1215 64 382 507 515 1451 472 447 1480 479 477 429 239 1415 147 1481 1365 1359 1391 1378 827 0\n1483 3 40 -82 -89 -19 -78 -39 -33 -67 41 -58 0 1471 147 14 20 1348 22 307 411 93 64 1365 1359 1391 1378 827 0\n1484 18 -19 -145 -78 -39 83 -33 -67 41 -58 0 1471 499 506 1452 14 20 1348 415 436 137 102 79 46 70 69 66 64 1407 1438 1482 502 489 431 1402 1377 147 1483 1481 447 472 473 1451 460 510 456 484 454 474 423 426 1384 1385 0\n1485 161 163 38 -176 -157 74 41 -58 0 65 593 592 1458 1069 604 599 1078 1129 1151 0\n1486 -169 -33 -67 74 41 -58 0 1471 14 13 182 1411 530 307 1215 70 69 571 573 1478 540 1201 20 22 79 1064 535 137 1479 1485 543 173 1444 1484 0\n1487 -39 -184 41 26 0 618 22 1064 606 604 614 599 601 595 1077 1069 548 1238 0\n1488 163 38 -184 41 26 0 618 606 604 614 599 601 595 1077 1069 548 1238 0\n1489 -164 45 -157 74 80 -58 0 65 1129 557 1151 0\n1490 82 65 63 -161 -165 -163 -58 0 1471 70 69 561 1067 190 552 543 127 0\n1491 -177 -165 -163 38 41 -58 0 1471 1077 70 69 593 595 548 77 82 1490 146 148 552 543 177 0\n1492 164 38 -184 41 -58 0 65 1488 618 607 599 597 609 1491 614 0\n1493 38 -33 -67 74 41 -58 0 1471 70 65 69 1486 580 590 1460 1074 307 411 1487 1427 182 1411 540 169 1373 14 13 530 1215 1488 1492 1489 40 41 48 103 1365 1069 1226 552 595 75 616 614 1348 1459 1152 588 148 578 543 569 992 535 0\n1494 -33 -67 74 41 -58 0 1471 307 411 169 530 1215 70 69 66 65 64 14 1486 580 590 1460 618 1074 1487 1373 1427 418 430 439 490 440 1493 16 18 45 78 101 144 1348 1479 1151 415 502 1120 436 507 1384 446 1451 423 471 454 460 456 0\n1495 -185 41 -58 0 69 616 620 606 609 1079 1491 601 0\n1496 -84 -161 57 0 1471 163 180 543 0\n1497 -86 -70 -40 -19 -66 30 -18 -77 -172 39 41 -58 0 125 580 571 137 535 14 8 573 577 66 1445 64 382 74 172 411 540 1398 290 750 1351 531 288 311 920 0\n1498 -4 -70 -40 -19 -66 30 -18 -77 -172 39 -58 0 125 580 571 137 535 14 8 573 577 66 1445 64 382 34 531 114 288 311 540 1398 920 0\n1499 -90 -14 -83 -42 -70 -40 -19 -66 -32 -18 -77 -58 0 74 283 413 763 0\n1500 -83 -42 86 -70 -40 -19 -66 -32 30 -18 -77 -58 0 74 283 137 64 382 66 1410 1499 1431 279 758 0\n1501 89 -177 -163 38 74 41 -58 0 1471 595 1069 1215 65 70 593 1496 557 1492 1460 590 580 571 577 586 567 1491 564 563 1064 66 1445 74 69 64 543 1383 125 127 137 1228 535 8 9 14 1137 528 88 91 1389 548 552 1497 1498 1360 1372 283 1500 1320 1422 1411 1426 761 0\n1502 -67 -158 74 41 -58 0 1494 1137 0\n1503 -177 -163 38 74 41 -58 0 1215 70 69 65 593 595 1069 1496 557 1492 1460 586 590 567 577 1501 177 1502 528 88 91 548 552 47 0\n1504 -89 -66 -157 -178 -163 74 80 -58 0 92 91 69 177 190 552 48 146 1489 561 597 0\n1505 -46 89 36 -157 38 74 41 -58 0 1471 1215 70 47 48 127 548 1489 543 599 592 609 1457 0\n1506 -66 -157 -163 38 74 41 -58 0 1471 1503 1458 607 1215 70 69 88 91 92 1504 1505 552 103 186 1489 599 597 609 1077 561 1457 548 148 592 543 0\n1507 -67 39 74 41 -58 0 1495 1459 588 70 69 65 182 1502 1411 577 576 590 573 1460 540 1074 0\n1508 -157 -163 38 74 41 -58 0 1064 1507 1506 528 0\n1509 45 40 -164 -184 74 41 -58 0 1215 70 69 65 557 1238 1496 1226 0\n1510 -163 38 74 41 -58 0 1471 1495 1459 74 70 69 67 65 1064 1503 1507 1508 529 567 273 586 585 1460 577 580 1074 1492 614 571 1075 609 109 110 114 135 1411 1426 601 1077 1509 40 103 1365 1226 48 552 1152 75 148 1403 535 543 14 1356 865 531 0\n1511 -32 -8 -42 -82 -19 -89 -72 -3 -45 -66 74 -58 0 179 1426 1411 1349 944 0\n1512 33 -82 -19 -89 -72 -3 -45 -66 -159 -158 74 -58 0 119 386 1426 1411 135 114 110 109 67 531 272 1511 535 1355 945 0\n1513 -89 -72 39 -45 38 74 41 -58 0 1426 1411 135 110 1510 1069 595 1458 604 601 1365 65 1488 1460 586 567 590 577 1502 528 92 580 571 555 1215 190 1444 561 1512 14 282 1352 535 943 0\n1514 -72 39 -45 38 74 41 -58 0 1471 1069 595 1458 1365 65 1510 1488 1460 586 567 590 577 1502 528 580 571 606 1457 1485 556 553 1215 74 70 69 67 109 110 114 135 1411 1426 1513 1383 543 125 148 535 1138 1416 14 1356 531 952 0\n1515 -42 -14 -32 -90 -77 -18 -91 -83 -3 -45 -66 -58 0 413 74 283 946 0\n1516 -32 33 -90 -77 -18 78 -91 -83 39 -3 -45 -66 -158 41 -58 0 413 8 11 1410 1515 531 1351 948 0\n1517 42 -30 -1 33 -90 -77 -18 -91 -83 -3 -45 -66 -158 -58 0 115 3 413 531 249 940 0\n1518 33 -90 -77 -18 78 -91 -83 39 -3 -45 -66 -159 -158 41 -58 0 413 125 74 65 1516 210 535 1517 783 283 0\n1519 -33 28 78 -159 0 13 14 535 0\n1520 -86 -42 -30 -1 -77 -18 -91 -83 -3 -45 -66 -58 0 74 283 411 747 0\n1521 32 90 -77 -18 78 -91 -83 -3 -45 -66 -159 -158 -58 0 288 125 1519 64 382 74 66 65 210 535 3 531 283 1520 1431 279 755 0\n1522 86 -14 -42 -32 90 -77 -18 -91 -83 -3 -45 -66 -58 0 74 288 67 1356 64 382 66 1431 279 912 0\n1523 39 -164 38 74 41 -58 0 1471 1215 65 1510 1488 1460 586 567 1489 1069 595 1458 1365 590 577 1502 528 70 606 1457 1485 1496 580 573 571 556 553 74 69 67 1514 540 156 1138 190 1160 1439 543 125 1519 1518 288 1521 8 11 1356 531 1410 1522 411 904 0\n1524 -86 -82 -19 -89 -78 -11 -33 -39 -3 -45 -66 -58 0 1471 20 66 1445 65 64 1342 411 905 0\n1525 90 -39 -165 -3 -45 -164 -66 -159 -161 -158 80 -58 0 1471 117 386 36 20 19 92 70 1496 66 1445 64 382 65 288 531 303 1342 1519 137 1160 543 1389 561 1524 279 1435 913 0\n1526 -33 -78 -89 -82 -19 -90 -39 -3 -45 -66 67 -58 0 1471 65 1350 413 282 941 0\n1527 -78 -89 -82 -19 -90 -39 -3 -45 -66 67 -172 -58 0 1471 413 152 117 111 19 65 1350 1526 1320 224 782 0\n1528 91 -90 -39 -165 -3 -45 -66 67 -161 -172 74 80 -58 0 1471 413 152 111 21 20 19 92 580 571 70 1389 561 148 543 1527 336 1519 535 1403 942 1320 0\n1529 -164 38 74 41 -58 0 1471 65 1510 1488 1460 586 567 590 577 1502 528 70 606 1457 1485 1496 580 571 1215 69 1489 1365 1069 595 1458 604 601 1523 19 20 21 111 152 1525 413 1528 190 1160 1425 1439 543 336 1519 535 949 1320 0\n1530 38 74 41 -58 0 65 1510 1456 1488 1460 586 590 567 577 1502 528 88 1529 599 597 604 1077 1458 548 595 0\n1531 164 67 -38 74 -58 0 1471 69 1079 1456 151 144 101 45 25 22 17 16 70 558 599 597 604 618 1458 1460 593 586 590 567 577 580 528 571 573 92 1387 540 561 109 114 119 135 1411 1426 190 1439 1519 535 543 531 291 1344 779 0\n1532 -172 -181 -91 -158 -45 -66 -38 74 -58 0 69 1439 526 529 568 549 151 45 22 17 16 580 591 571 573 1461 540 619 109 114 119 135 1411 1426 596 1519 535 546 531 291 1349 1430 781 0\n1533 53 -90 -14 -16 -32 33 -77 -18 -91 -158 -45 -66 -38 -58 0 413 9 387 8 531 291 789 0\n1534 -90 -14 -16 -32 33 -77 -18 -91 -158 -45 -66 -38 41 -58 0 22 413 1533 1372 950 0\n1535 86 -8 -42 90 -14 -16 -32 -77 -18 -91 -45 -66 -38 -58 0 64 382 66 1431 279 752 0\n1536 -8 -42 -58 90 -14 -16 -32 -77 -18 -91 -45 -66 -38 0 1535 411 744 0\n1537 -159 33 -77 78 169 -18 -91 -158 -45 -66 -38 41 -58 0 17 16 66 1445 64 382 574 535 541 8 9 1414 1398 1534 288 531 272 1536 0\n1538 33 -77 78 169 -18 -91 -158 -45 -66 -38 41 -58 0 151 22 1495 1459 588 578 65 1537 538 569 210 540 109 114 119 1411 1426 223 531 291 785 0\n1539 -165 -158 -66 74 41 -58 0 1471 1215 1530 22 1507 1531 529 1489 144 1151 92 151 25 18 16 1495 1459 588 578 66 1445 70 69 65 64 602 561 605 190 1439 1532 590 581 1460 1226 1160 543 1538 282 1352 1342 1519 569 540 1411 1426 787 0\n1540 -77 -42 91 -45 -66 -38 -58 0 151 22 45 144 101 69 1138 618 1460 590 580 573 540 119 571 16 135 1519 114 1411 291 17 535 1426 353 1406 1428 760 0\n1541 -158 -66 74 41 -58 0 1471 1215 1530 22 1507 1531 529 1489 151 144 101 45 17 16 70 69 1539 564 353 1138 618 1458 1460 593 590 580 571 573 540 109 114 119 135 1411 1426 1519 535 291 531 1540 543 1396 258 780 0\n1542 158 -38 41 -58 0 151 101 22 18 1495 1459 588 532 1220 576 540 573 0\n1543 74 41 -58 0 1471 1495 1459 70 69 1530 16 17 18 22 25 144 1079 1507 1531 1542 1541 528 273 567 586 585 1139 1460 580 109 114 119 135 1411 1426 618 1226 1509 571 1519 535 291 604 84 531 601 561 190 300 1439 543 860 0\n1544 -38 66 41 -58 0 1471 1543 129 70 178 543 136 122 121 69 25 1542 1226 1460 586 590 567 580 528 571 1137 1519 0\n1545 -184 38 161 84 41 26 0 593 612 614 592 609 1078 0\n1546 66 41 -58 0 1471 1543 129 70 178 543 162 136 121 65 1544 1545 1460 586 590 567 580 528 571 1519 577 1137 0\n1547 -86 -42 -8 -14 -32 -12 -46 -91 -83 -3 41 -58 0 1546 1543 411 906 0\n1548 90 -12 -46 -91 -83 -3 -172 41 -58 0 1543 121 580 571 136 43 535 8 66 1445 1519 1225 1397 577 1546 74 67 288 1356 531 1547 279 1433 914 0\n1549 -42 -90 -14 -32 -12 -46 -91 -83 -3 41 -58 0 413 1546 1543 74 283 963 0\n1550 -179 38 41 -58 0 1471 1543 136 121 65 162 129 70 178 543 1545 1460 590 580 571 1519 577 1546 92 91 123 66 1445 69 601 1078 1077 592 1369 1457 1225 606 1201 156 1067 561 552 1387 43 535 1397 8 9 387 1548 413 1549 531 249 962 0\n1551 42 72 38 41 -58 0 1471 1543 66 1445 69 129 70 178 543 593 1458 1550 604 1215 559 609 1457 592 1068 1228 1397 65 162 1545 1460 590 580 573 1064 540 121 571 136 535 9 387 8 1546 602 563 564 1138 122 548 1377 1389 1519 577 531 249 288 311 924 0\n1552 -90 72 38 41 -58 0 1471 74 1551 283 1543 66 1445 69 129 70 178 543 593 1458 1550 604 1215 559 609 1457 592 1068 1228 1397 65 162 1545 1460 590 580 573 1064 540 121 571 136 535 1546 602 563 564 1138 122 548 1377 1389 413 767 0\n1553 86 72 38 41 -58 0 1471 1552 74 1551 283 1543 66 1445 69 129 70 178 543 593 1458 1550 604 1215 559 609 1457 592 1068 1228 1397 65 162 1545 1460 590 580 573 1064 540 121 571 136 535 1546 602 563 564 1138 122 548 1377 1389 279 1433 759 0\n1554 72 38 41 -58 0 1471 1543 121 65 162 129 70 178 543 1545 1460 590 580 571 136 69 593 1458 1550 604 1215 559 609 1457 592 1068 1228 535 1546 602 563 564 1138 122 548 1377 1389 1064 573 66 1445 74 540 1397 1551 283 1553 411 751 0\n1555 38 41 -58 0 1471 1546 1543 129 70 178 543 593 1458 559 162 136 122 121 1215 74 69 67 65 1545 1460 590 577 580 571 1519 1550 609 602 604 1457 563 564 592 1389 548 1068 1377 1228 1138 535 8 1554 114 1411 1426 1416 1356 531 772 0\n1556 41 -58 0 1471 70 69 1543 121 122 129 136 178 543 1555 22 25 45 101 144 151 1226 1152 1460 590 580 571 573 1519 540 1222 0\n1557 70 -72 -74 -58 0 1471 1556 29 387 1426 37 114 313 425 1118 123 1364 419 438 440 443 467 1449 178 143 68 1170 147 188 1429 1382 434 426 492 476 495 487 499 515 514 500 1450 496 468 494 460 433 456 1389 453 308 424 0\n1558 66 124 -70 -92 -58 0 1556 30 68 308 1388 424 423 455 0\n1559 8 -82 -72 -74 -58 0 1471 1426 1557 1556 1118 123 1364 419 438 440 443 29 387 37 114 313 425 475 484 143 1442 433 493 495 499 510 1451 469 461 457 1558 1411 74 67 1356 291 209 776 0\n1560 -82 -72 -74 -58 0 1471 1426 1557 1556 1118 123 1364 419 438 440 443 29 387 37 114 313 425 475 484 143 1442 433 493 495 499 510 1451 469 461 457 1558 472 449 1411 110 28 67 1559 935 209 1355 415 416 437 0\n1561 -72 -74 -58 0 1471 1556 1118 123 1364 419 438 440 443 467 1449 143 29 387 37 114 1426 313 425 475 1557 1442 433 493 495 1560 1370 1401 429 431 477 489 479 502 485 515 0\n1562 -74 -58 0 1471 1556 29 387 1118 153 37 32 28 66 1445 70 69 121 123 129 136 143 178 1364 543 593 616 1459 588 578 1561 247 1075 540 567 573 569 580 576 1519 590 1137 531 1460 528 288 311 614 91 606 609 1228 552 601 1397 535 1442 1166 926 0\n1563 -82 -70 -184 -58 0 1471 177 103 1562 70 65 148 1129 543 599 593 609 614 0\n1564 -92 -53 -32 -14 -77 -80 -70 -16 -58 0 1471 1556 33 255 419 438 440 443 430 490 1562 1437 432 497 502 507 1451 469 461 457 414 1558 768 0\n1565 -53 -32 -58 -14 -77 -80 -70 -16 0 1564 311 0\n1566 -70 72 -58 0 1471 1556 153 32 540 573 580 590 1460 618 607 29 387 247 1562 37 28 66 1445 64 382 70 65 99 100 103 161 177 1563 1166 601 597 609 557 620 614 1459 593 588 543 578 576 137 1398 569 1519 535 531 1565 0\n1567 89 146 70 -58 0 1556 1170 1562 1383 1429 432 434 498 492 0\n1568 19 -32 -53 72 -58 0 1566 1556 29 387 247 430 490 1562 1170 148 1349 427 221 428 478 481 483 1447 503 1567 311 288 96 188 149 153 32 540 573 580 64 382 68 66 65 1441 1389 308 528 868 567 1129 585 599 1459 609 620 0\n1569 -32 -53 72 -58 0 311 288 1556 1566 1170 148 147 29 387 247 430 490 1562 68 1349 221 427 428 478 481 483 1447 503 1567 1568 433 493 495 502 1448 515 486 1449 474 465 426 460 1382 456 793 453 308 424 0\n1570 66 -45 131 -53 72 -58 0 1569 311 96 53 1566 1556 153 32 540 573 580 1118 69 68 308 528 424 567 453 585 1334 456 1459 1353 460 620 416 471 606 448 552 437 75 415 1345 0\n1571 113 -45 32 33 -58 0 1556 29 28 64 435 436 416 415 1341 1345 0\n1572 -45 -14 -89 -53 72 -58 0 1556 29 387 247 430 490 501 428 478 479 482 510 1451 1569 311 288 53 1566 1170 188 149 148 1562 64 382 1570 1389 433 493 495 502 511 1450 470 448 1571 445 467 1449 515 483 481 427 1395 1353 416 792 437 1345 415 0\n1573 179 67 72 -58 0 1566 1556 153 32 540 573 580 590 1460 618 1118 69 609 604 620 552 1459 91 585 528 567 0\n1574 66 -89 -53 72 -58 0 65 1562 1556 1566 1170 96 1573 599 1129 1569 64 382 1572 1394 1345 311 288 53 153 32 540 573 580 29 387 247 1118 69 68 308 528 567 585 1334 1459 1353 1409 620 708 606 552 0\n1575 -2 -89 -53 72 -58 0 1556 1566 1170 149 188 1574 1389 65 1562 96 1573 599 1129 1569 64 382 1572 1394 1345 311 288 29 387 247 2 790 1409 0\n1576 -89 -53 72 -58 0 65 1562 1556 1566 1170 96 1573 599 1129 1569 311 288 188 149 148 29 387 247 64 382 1572 1394 1345 1574 1389 1575 1357 1395 791 0\n1577 -53 72 -58 0 1471 1556 1566 1170 148 153 32 540 573 580 590 1460 1118 70 69 96 1576 543 593 1075 614 567 606 528 552 91 0\n1578 -92 -1 -66 72 -58 0 1471 1556 28 1577 37 153 32 540 573 1566 69 1118 91 552 606 620 1459 588 576 531 29 303 425 475 387 247 430 490 1170 149 188 1389 433 493 495 502 415 436 445 467 1449 515 485 479 478 428 222 148 70 580 590 1460 614 593 543 65 1562 98 1573 599 1129 414 788 0\n1579 86 -1 -66 72 -58 0 1471 1578 413 1556 28 1577 37 153 32 540 573 1566 69 1118 91 552 606 620 1459 588 576 531 29 303 425 475 387 247 430 490 1170 149 188 1389 433 493 495 502 415 436 445 467 1449 515 485 479 478 428 222 148 70 580 590 1460 614 593 543 65 1562 98 1573 599 1129 64 382 66 279 1435 754 0\n1580 -1 -66 72 -58 0 1471 1556 28 1577 37 153 32 540 573 1566 69 1118 91 552 606 620 1459 588 576 531 1170 148 70 580 590 1460 614 593 543 29 387 247 430 490 149 188 1389 433 493 495 502 65 1562 98 1573 599 1129 303 425 475 415 436 445 467 1449 515 485 479 478 428 222 1579 411 746 0\n1581 -86 -66 72 -58 0 1471 64 382 65 1562 1556 1566 1170 98 1573 599 1129 28 1577 37 153 32 540 573 69 1118 91 552 606 620 1459 588 576 531 14 1580 1345 1394 148 70 580 590 1460 614 593 543 29 303 149 188 1389 387 247 411 902 0\n1582 90 -66 72 -58 0 1471 1581 64 382 65 1562 1556 1566 1170 98 1573 599 1129 28 1577 37 153 32 540 573 69 1118 91 552 606 620 1459 588 576 531 14 1580 1345 1394 148 70 580 590 1460 614 593 543 29 303 149 188 1389 387 247 66 279 1435 910 0\n1583 -66 72 -58 0 1471 1577 1556 1566 1170 188 149 148 153 32 540 573 580 590 1460 29 387 247 1562 1118 37 28 64 382 70 69 65 91 98 1389 303 552 1573 606 599 620 614 1129 1459 593 588 543 576 531 14 1580 1345 1394 1582 413 947 0\n1584 129 72 -58 0 1471 1583 1577 1556 1566 1170 147 465 1113 460 75 456 1367 454 423 0\n1585 14 -33 -45 72 -58 0 14 1583 1556 64 382 1394 222 1345 1128 0\n1586 28 13 -33 -45 72 -58 0 14 1583 1556 1566 1170 1562 1345 1403 1128 0\n1587 -33 -19 -45 -89 72 -58 0 1556 29 387 247 430 490 433 493 495 502 1584 1449 515 483 1583 1566 1170 147 1585 428 478 479 481 485 427 475 425 282 307 312 1586 75 974 1367 0\n1588 13 33 -45 -89 72 -58 0 1566 69 1556 1118 1583 28 1577 37 531 1095 1459 620 606 552 75 29 387 153 32 540 573 576 1455 567 528 312 307 1228 272 1170 148 247 1562 1349 1403 1353 1345 813 0\n1589 -19 -45 -89 72 -58 0 1584 1449 1583 1577 1556 29 387 247 430 490 1118 37 28 66 1445 64 382 69 433 493 495 502 515 483 1587 531 1095 1459 620 606 1228 1588 427 1393 481 428 478 0\n1590 33 -45 -89 72 -58 0 1556 1566 1170 1589 1423 76 75 1583 1577 153 32 540 573 29 387 247 37 28 66 1445 64 382 531 272 1588 1453 576 1393 569 1455 567 528 307 312 811 1353 1345 535 813 0\n1591 -45 -89 72 -58 0 1471 1556 29 387 247 430 490 501 1584 1449 517 1566 1170 66 1445 65 64 1589 1423 75 1590 1585 1342 1586 428 427 478 481 486 475 425 282 307 312 817 0\n1592 179 72 -58 0 1471 1583 1577 1566 1556 153 32 540 573 580 590 1460 618 1118 37 28 66 1445 69 65 64 609 604 620 552 1459 75 588 1095 578 531 569 1342 1519 1128 0\n1593 72 -58 0 1471 1562 1556 29 387 1118 153 37 32 28 70 69 65 247 540 430 573 490 580 590 1460 1566 1170 148 1577 1583 1584 1449 1592 599 1129 1591 543 1567 593 503 616 614 512 1459 606 482 1095 552 480 531 75 427 1586 0\n1594 -63 28 -33 -58 0 1471 1593 135 1519 571 580 66 1445 65 64 1342 1556 29 387 114 37 1426 313 172 307 1411 1562 70 68 91 107 308 528 1170 567 148 1403 585 1459 616 620 593 609 543 599 711 1129 0\n1595 -182 63 -184 -58 0 1556 1118 69 606 609 552 601 1563 1166 0\n1596 -70 28 -33 -58 0 1471 1593 172 307 135 1519 571 580 590 1460 1594 1595 620 1459 585 567 528 70 614 593 1496 618 607 66 1445 65 64 1342 1556 29 387 114 37 1426 313 1411 1562 33 103 177 1437 255 1563 543 1166 774 597 557 0\n1597 28 -33 -58 0 1471 1556 29 387 1593 114 37 1426 313 172 307 1411 135 1562 1118 66 1445 70 69 65 64 1342 1519 571 580 590 1460 618 1594 1595 620 614 1459 593 585 567 528 1596 1170 552 148 1403 1423 604 543 599 794 1129 0\n1598 -184 -33 -58 0 1471 532 1593 541 1597 536 574 581 75 69 1556 1118 99 552 606 1170 1423 147 125 29 387 114 37 1426 313 1411 1562 526 70 68 65 618 1461 614 604 591 593 599 568 543 1129 529 308 1367 864 0\n1599 -164 -33 -58 0 1593 172 307 1598 1460 586 567 528 1597 75 1556 99 1170 1423 563 29 387 114 37 1426 313 1411 1562 551 65 1129 602 605 619 596 547 1383 1429 918 0\n1600 -33 -58 0 1471 1556 29 387 1593 114 37 1426 313 172 307 1411 1118 70 69 1597 75 99 125 1170 552 147 1423 1598 1460 586 567 528 1599 558 599 1364 1382 604 937 1458 543 593 0\n1601 -28 -58 0 1471 1556 1600 1299 590 1460 618 1593 114 29 272 28 37 531 387 1426 313 1411 1562 1118 70 69 65 64 75 99 125 1341 1595 1170 552 620 614 1423 604 1459 593 599 1095 543 1129 796 0\n1602 -66 -82 -58 0 1556 1600 1299 590 1460 1563 1593 114 29 272 422 458 460 465 1449 387 37 1426 313 425 475 1601 135 1562 1403 427 480 485 515 500 1567 188 149 618 28 531 1411 110 1118 69 65 91 1389 1595 552 620 604 1459 599 588 1129 576 795 571 535 0\n1603 -82 -58 0 1601 1593 114 1556 29 1600 272 422 458 460 465 1449 1299 590 1460 28 37 531 387 1426 313 425 475 172 307 1411 135 110 1562 68 65 1563 1403 427 480 485 515 500 1567 1602 308 528 1095 567 1459 1455 620 1094 609 1595 535 599 870 1129 0\n1604 -58 0 1471 65 70 1556 28 29 33 37 387 1562 1593 110 114 135 1411 1426 313 1600 1299 531 272 590 1460 618 607 1601 1603 1170 1166 103 107 161 177 1437 255 597 1595 557 620 614 1459 593 588 1095 543 576 777 571 535 0\n1605 -172 78 28 -41 0 580 1299 571 1519 0\n1606 -159 89 45 -164 -66 -72 82 28 -41 0 1604 1471 153 31 92 113 172 280 525 566 135 1605 585 1459 620 609 601 561 1425 189 187 275 1067 616 593 29 387 114 37 1426 313 1411 110 1519 535 291 10 557 124 129 1152 543 718 0\n1607 26 89 45 -164 -66 -72 82 28 -41 0 1604 1471 28 114 37 113 172 280 525 566 1455 1606 571 576 531 153 31 92 135 1605 585 1459 620 609 601 561 1425 189 187 275 1067 616 593 29 387 1426 313 1411 27 26 1342 557 124 129 1152 543 713 0\n1608 89 45 -164 -66 -72 82 28 -41 0 1604 1471 113 172 280 525 566 135 1605 585 1459 620 609 601 1067 616 593 1607 55 61 1152 543 127 0\n1609 -33 -54 -45 -91 -66 -72 28 -41 0 1604 1471 190 113 172 280 525 566 135 1605 585 1459 616 593 62 543 38 153 31 1425 275 29 387 114 37 1426 313 1411 27 26 1342 707 0\n1610 -45 -91 -66 70 -72 28 -41 0 1604 1471 190 153 31 1425 172 280 275 91 113 525 566 135 1605 585 1459 620 606 616 593 1455 29 387 114 37 1426 313 1411 110 28 48 62 552 543 1609 531 291 576 712 571 535 0\n1611 -66 -72 82 28 -41 0 1604 113 172 280 525 566 135 1605 585 1459 620 609 599 601 1067 92 561 190 1610 1608 0\n1612 -72 82 28 -41 0 1604 113 135 172 280 307 525 1605 1454 1611 565 528 0\n1613 -67 78 160 28 -41 0 1604 573 37 28 96 1324 566 1455 578 576 569 531 1519 0\n1614 78 66 72 28 -41 0 1604 153 32 540 573 1070 37 28 1613 528 567 565 1455 578 576 569 1519 531 54 73 525 0\n1615 -53 -156 0 1604 54 73 525 0\n1616 -57 45 -182 74 82 0 609 601 1067 599 61 63 85 1152 561 160 187 557 0\n1617 26 -65 -46 -89 84 45 -51 -33 -164 -11 -78 -16 -41 0 1471 1604 305 278 136 1350 557 268 733 0\n1618 45 -51 -33 -182 -161 -11 -78 -16 82 -41 0 1471 305 278 609 601 1066 1067 599 137 136 27 1446 26 382 1616 1496 543 175 190 1152 561 1617 138 1370 1441 890 0\n1619 157 -78 72 82 -41 0 1604 1471 137 153 32 540 573 580 29 387 247 1070 37 28 567 565 1455 1075 585 1337 576 593 1459 620 606 609 601 1067 1066 1615 531 72 525 1618 48 62 552 543 175 0\n1620 -45 63 70 -163 -161 77 0 1471 48 62 552 543 175 0\n1621 26 -65 -46 -89 84 45 -164 -33 -67 -78 -16 -41 0 1471 1604 29 387 312 276 307 136 1350 557 268 723 0\n1622 66 82 28 -41 0 1604 1471 153 32 1612 540 573 580 29 387 247 1614 136 137 1619 528 307 276 1324 312 566 1455 1075 585 576 593 1459 1137 620 606 609 599 601 1067 1066 1620 1616 1496 543 175 190 1152 561 1621 138 1370 1444 722 0\n1623 -174 51 169 -41 0 1604 580 37 28 588 585 576 566 1615 525 531 72 0\n1624 -78 89 -161 -182 63 82 0 1471 609 601 1067 606 136 137 1620 543 1616 0\n1625 -33 78 51 160 28 0 1604 72 1519 525 569 566 578 1455 0\n1626 -57 45 156 82 28 -41 0 1604 28 153 32 1612 540 1622 90 91 573 1623 1459 620 616 593 92 609 601 561 190 1624 1625 37 566 1455 576 531 311 288 578 569 527 275 31 1425 1067 29 387 247 63 1616 1152 43 1409 535 716 0\n1627 45 156 82 28 -41 0 1471 1622 92 153 32 1612 540 573 90 1623 1459 620 609 601 561 189 187 190 1067 599 606 616 593 91 1626 543 127 129 552 557 55 0\n1628 156 82 28 -41 0 1604 153 32 1612 540 1622 90 91 573 1623 1459 620 616 593 92 609 601 561 190 1624 1625 31 1425 1067 606 29 387 247 37 28 527 566 275 1455 578 576 569 531 288 311 1627 48 1620 552 57 1409 535 710 0\n1629 -45 82 28 -41 0 1604 153 32 1612 540 28 1622 90 91 573 1623 1459 620 616 593 92 609 601 561 190 1624 1625 37 1628 1615 531 1453 569 29 387 525 289 280 1337 31 1425 1067 606 247 48 1620 552 57 1409 535 969 0\n1630 -77 45 84 80 70 -164 -163 63 0 127 129 552 557 55 0\n1631 82 28 -41 0 1604 1471 29 387 153 37 32 31 28 1612 247 540 573 1622 90 91 92 1623 1459 616 620 593 606 609 599 601 1067 561 190 187 189 1425 1624 1625 1628 1337 1615 525 531 280 289 1453 569 1629 1630 543 63 1616 1152 43 1409 535 968 0\n1632 51 -174 28 -41 0 1604 153 32 1623 573 540 135 172 1605 280 585 525 566 0\n1633 -174 28 -41 0 153 32 1632 90 95 113 528 540 567 573 585 580 0\n1634 -156 -158 51 -41 0 1604 37 28 1615 525 531 72 0\n1635 -167 66 0 1604 566 567 1324 528 0\n1636 -67 -63 70 45 28 -41 0 1604 1471 91 1635 1455 1631 1378 1633 1459 620 609 599 616 593 148 147 29 387 153 32 182 307 276 312 1411 1427 540 1614 573 136 576 1129 1137 61 1379 543 724 0\n1637 169 -63 70 45 28 -41 0 1604 1471 91 1636 528 1635 1455 1631 1378 1633 1459 620 609 599 616 593 148 147 29 387 37 28 580 576 1454 565 1337 1615 1634 531 113 278 305 247 1614 136 1129 61 1379 894 543 0\n1638 -63 70 45 28 -41 0 1604 153 32 91 1636 528 1637 573 540 113 135 172 1605 280 1454 525 565 0\n1639 -54 45 -164 84 80 0 55 124 557 0\n1640 -70 -161 77 0 1471 106 177 543 0\n1641 45 28 -41 0 1631 148 1633 1459 616 593 1640 620 609 599 606 165 149 146 1639 1638 552 0\n1642 -72 157 28 -41 0 1604 113 135 172 1605 280 1454 525 565 0\n1643 157 28 -41 0 1471 1604 1631 148 1633 1459 616 593 620 606 1640 1641 1620 91 1635 1455 38 62 543 268 29 387 153 37 32 28 1642 1070 247 540 1614 565 573 1350 1337 1615 576 1634 531 278 305 737 0\n1644 28 -41 0 1604 1471 29 387 153 32 1631 148 1633 1459 616 620 593 606 1640 1641 38 62 1620 543 91 268 1635 1455 1643 528 182 307 276 312 1411 1427 540 1614 573 1350 725 576 1137 0\n1645 169 -41 0 1644 56 99 42 75 552 606 620 1459 580 1623 585 90 1635 0\n1646 -45 -66 -41 0 1604 1471 153 32 1645 573 540 172 280 275 92 1644 56 99 42 75 552 113 525 566 586 1460 618 604 601 606 614 593 620 1459 585 1299 29 387 114 37 1426 313 1411 125 62 141 1380 543 190 1444 561 702 0\n1647 -66 -41 0 1604 1644 56 99 42 75 552 153 32 1645 573 540 113 172 280 525 566 586 1460 618 604 599 121 1 1646 1129 1138 187 189 557 0\n1648 -41 0 1604 32 153 1644 42 56 75 99 552 606 620 1459 583 1645 573 540 113 172 280 307 525 1647 565 528 0\n1649 46 26 -91 54 82 72 167 0 1648 586 1460 1487 186 184 1152 552 620 1488 1459 151 585 540 580 573 0\n1650 160 38 26 84 72 167 0 1648 542 573 1075 580 595 585 1078 1459 609 620 0\n1651 -185 38 26 84 0 1648 616 620 595 609 1078 0\n1652 26 -91 54 82 -67 167 0 1604 1471 1648 190 189 184 183 307 171 381 411 169 168 182 1411 276 586 1460 1487 1373 1649 42 45 127 1545 543 1650 540 1651 1459 585 577 580 1137 571 1519 1342 1624 1407 614 730 595 548 0\n1653 -91 80 54 82 -67 66 0 1604 1648 1471 276 421 450 307 1635 586 1460 183 184 185 186 190 1652 15 61 120 1379 1226 300 543 1479 426 423 127 499 474 454 1343 484 456 419 510 463 438 1451 440 469 443 0\n1654 40 78 119 46 -26 54 -67 167 0 444 15 1 307 171 381 169 168 182 1411 95 93 1343 419 438 440 442 446 417 435 1371 1359 416 540 1334 1340 1625 0\n1655 78 119 46 -26 54 -67 167 0 10 1 586 1460 618 1654 1077 601 609 604 620 1228 1459 535 585 571 580 0\n1656 161 36 54 -184 0 1648 593 1226 614 1077 609 601 0\n1657 70 63 46 36 54 82 72 167 0 1648 586 1460 618 1152 552 620 614 604 1459 595 601 585 1077 580 548 573 22 151 540 0\n1658 63 46 -26 91 80 54 82 -67 167 0 1604 586 1460 15 1656 120 276 421 450 462 182 1411 307 1440 433 493 1657 1640 1437 137 432 1655 498 471 500 1451 507 0\n1659 46 -26 91 80 54 82 45 -67 167 0 1604 1648 1471 586 1460 15 1656 157 61 1 307 411 169 182 1411 276 1658 78 79 107 1386 1373 1152 620 614 1459 595 585 548 577 580 1137 571 573 1519 540 137 1402 884 543 0\n1660 -26 91 80 54 82 45 -67 167 0 1604 1648 1471 307 411 169 182 1411 276 586 1460 1 15 61 1656 1659 45 46 47 80 127 1366 1373 548 1440 543 595 616 1075 614 1459 609 585 601 577 580 561 1137 571 886 1519 0\n1661 -46 36 26 91 54 82 72 167 0 1648 586 1460 1487 45 47 160 1650 548 540 595 1074 614 85 609 561 601 0\n1662 36 77 91 80 54 82 45 -67 167 0 1604 1648 1471 307 169 586 1460 1660 1487 1373 171 381 411 168 182 1411 276 618 607 1656 1640 1661 1152 1657 620 614 75 78 1066 1459 595 597 585 548 577 580 1137 571 573 1342 1519 540 136 1074 557 265 727 0\n1663 -36 26 91 82 45 -178 0 82 158 1076 561 597 0\n1664 80 54 82 45 -67 66 0 1648 182 1411 95 1635 586 1460 618 607 1653 1660 1487 1663 1661 1662 125 128 129 137 163 1074 557 540 597 573 1625 1077 1067 1136 0\n1665 -80 72 167 0 1648 586 1460 138 140 155 164 1487 1650 540 0\n1666 84 -54 -67 167 0 1648 1471 175 63 58 56 55 586 1460 1545 1651 543 1459 137 585 577 580 1137 571 1519 0\n1667 -54 -67 167 0 1648 586 1460 612 58 63 1666 158 1496 593 592 614 548 609 1077 601 0\n1668 -82 -67 167 0 1648 1667 182 1411 586 1460 144 145 146 148 156 1075 593 595 1640 548 15 77 1488 552 0\n1669 -67 66 0 1648 1635 586 1460 182 1411 1665 1667 1668 1664 38 40 48 62 103 159 1487 1074 1657 540 78 1650 0\n1670 -45 82 54 66 0 1648 1604 1669 528 1635 586 1460 40 48 103 1152 620 614 1459 595 583 1069 565 78 1657 113 172 525 280 0\n1671 -38 82 54 66 0 1604 1669 528 1635 18 45 78 101 1657 1152 113 172 620 280 1459 525 583 565 0\n1672 -185 36 38 0 1648 616 620 595 609 548 601 1077 0\n1673 -72 -156 0 1604 113 172 525 280 0\n1674 26 -59 -182 36 80 82 54 66 0 1648 1635 1671 1672 1459 585 577 1669 528 583 565 1615 72 280 169 531 411 274 580 573 606 1064 1673 540 150 609 601 1067 1152 1366 160 43 42 599 571 1670 586 1460 1661 557 1074 300 136 1397 881 535 0\n1675 -59 -182 36 80 82 54 66 0 1648 1471 1635 1671 1672 1459 585 580 573 606 1064 1669 528 583 565 1673 540 150 609 601 1067 1152 1366 127 43 42 1066 571 1615 577 586 1460 1656 71 72 280 274 169 411 531 1674 10 61 1340 535 543 190 1444 561 888 0\n1676 -42 -65 -19 -89 -78 -26 -51 59 -83 -3 -46 0 10 305 278 43 283 900 1354 0\n1677 -26 59 -83 -3 -46 -165 -159 -158 -156 -161 80 82 0 1471 1604 525 52 387 305 278 51 127 43 42 1066 1615 10 61 535 543 190 1444 561 1676 1337 531 249 898 0\n1678 -182 36 80 82 54 66 0 1648 1604 1669 528 1671 1672 1459 583 565 1673 1635 585 580 573 571 1615 577 586 1460 1656 1670 606 609 1064 599 601 1067 1152 42 43 160 1366 540 150 1675 525 51 278 305 1677 1661 557 1074 300 136 1397 1519 535 271 531 891 0\n1679 84 -42 -8 -32 -14 -63 -57 26 -51 -83 -164 -40 80 45 0 128 305 278 183 1377 557 1390 734 0\n1680 78 -63 -57 26 -51 -83 30 -164 -40 -159 53 -158 80 45 54 0 75 305 278 51 1410 1519 535 271 531 1679 1438 1404 735 0\n1681 -42 -84 -18 -1 -78 -63 -57 -51 -83 30 -40 0 133 170 280 305 278 283 1354 741 0\n1682 26 -51 -83 -40 -159 -158 -156 80 45 54 -184 0 1471 1604 52 387 305 278 51 47 618 1077 601 604 1228 607 597 1615 1074 106 176 552 1680 136 1350 1407 557 1681 1337 531 249 739 0\n1683 42 -12 -63 -89 -17 -78 -26 -51 -83 -40 -158 -156 0 1604 52 387 305 278 51 1615 1337 531 249 896 0\n1684 -51 -83 -40 -159 -158 -156 -161 80 45 82 54 -184 0 1471 47 618 1077 601 604 1228 83 170 278 305 280 1682 1 10 61 157 535 1402 137 1640 543 552 1379 1683 283 1354 743 0\n1685 -26 -42 -10 -59 -83 -163 -40 -159 -161 82 54 0 1471 280 411 169 72 71 150 47 1228 83 1 10 61 157 1340 535 1402 137 1640 543 552 1379 731 0\n1686 -78 -63 -57 26 -42 -10 -59 -83 -164 -40 80 45 54 0 1471 176 280 411 169 71 387 72 136 1350 224 1407 557 729 0\n1687 -84 -32 -14 78 -63 -57 -42 -10 -59 -83 -40 54 0 75 280 411 1438 1404 879 0\n1688 36 80 82 54 66 0 1648 1604 1671 1670 1669 528 1635 586 1460 618 607 1656 1672 1459 583 585 565 577 580 1615 571 573 1673 1678 614 595 548 47 183 1077 601 597 604 1064 1228 540 1684 525 72 280 274 169 411 531 1685 1074 106 128 552 75 1686 1410 535 1687 557 1390 1377 878 0\n1689 78 -42 -10 -59 -83 -159 -57 -46 -18 -91 -36 0 280 411 43 42 122 1410 535 1400 880 0\n1690 -59 -83 -159 53 -57 -158 -46 -18 -91 -36 66 0 1471 15 71 72 280 274 387 169 411 531 1689 1350 728 224 0\n1691 -42 -78 -51 59 -83 -57 -46 -18 -91 -36 0 1471 15 1350 133 305 278 43 283 1354 740 0\n1692 -78 59 -83 -57 -158 -156 -46 -18 -91 -36 0 1471 1604 525 52 387 305 278 51 1615 15 1350 1691 1337 531 249 742 0\n1693 -36 82 54 66 0 1648 1471 1604 1671 1670 1669 528 1635 586 1460 618 607 15 77 122 158 1487 1663 1488 1545 1651 186 190 1439 1459 552 583 585 42 43 127 565 577 580 543 1615 1673 571 573 540 1690 525 51 278 305 1692 1410 1519 535 1400 271 531 732 0\n1694 82 54 66 0 1669 528 1635 1671 1693 1672 1688 1459 1665 583 1673 565 0\n1695 36 -82 66 0 1648 156 145 144 1669 528 1635 1672 548 1459 595 583 1075 565 1673 0\n1696 54 66 0 1648 1635 586 1460 1694 144 146 148 165 1695 15 77 1488 1545 552 1640 0\n1697 51 -36 66 0 1648 1471 1604 1696 57 175 63 1635 586 1460 58 55 158 1545 543 137 56 1651 1459 585 580 571 535 9 387 577 1669 528 583 565 1615 1519 8 531 59 1673 573 540 1410 618 607 40 148 1663 105 1385 60 1363 525 301 280 289 882 0\n1698 -36 66 0 1648 1471 1696 175 105 63 60 59 58 57 56 55 1669 528 1635 586 1460 618 607 40 158 1363 1385 1545 1651 543 1459 137 148 583 585 1663 565 577 580 1615 1673 571 573 1519 535 540 8 1410 531 1697 278 305 271 736 0\n1699 -91 -51 -77 66 0 1648 1696 56 1635 58 1698 1672 1459 585 580 571 137 1519 271 305 278 577 1669 528 583 565 1615 57 535 8 531 59 1673 573 540 1410 163 1665 554 105 81 586 1460 183 300 548 1371 895 595 1630 614 599 609 0\n1700 -51 -77 66 0 1471 1648 1696 59 1669 528 58 1698 1672 1459 583 565 1673 1635 585 580 573 540 57 137 1410 428 478 479 482 56 571 1519 163 105 81 63 60 271 422 458 460 465 1449 1699 1436 1424 434 433 494 496 500 515 511 1477 485 1450 438 474 468 419 426 443 1376 1381 441 1365 417 0\n1701 -45 -77 66 0 1604 1648 1696 57 1635 58 1698 1672 1459 585 580 571 56 137 535 9 387 1669 528 583 565 1700 525 289 280 577 1615 1519 8 531 301 59 1673 573 540 1410 1695 586 1460 84 1365 1069 595 614 609 601 561 300 883 0\n1702 164 66 0 1648 1698 1696 58 1635 586 1460 618 607 599 597 609 1077 614 548 595 0\n1703 -77 66 0 1702 1635 1669 528 1696 58 1698 1672 1459 583 565 1673 1665 554 105 81 163 1701 1630 0\n1704 66 0 1471 1648 1635 586 1460 612 1696 58 63 175 1698 1703 543 593 592 614 548 609 1077 601 0\n1705 -21 0 1704 87 0\n1706 -36 0 1704 88 0\n1707 -49 0 1704 89 0\n1708 -51 0 1704 90 0\n1709 -63 0 1704 91 0\n1710 -65 0 1704 92 0\n1711 157 0 1704 529 0\n1712 -71 0 1705 382 0\n1713 -22 0 1707 1445 0\n1714 -32 -83 -12 -54 -84 77 0 1709 1648 1706 1708 1604 1710 1704 165 189 561 601 609 63 1496 593 614 1460 590 577 586 566 1615 525 72 280 169 531 411 71 387 1673 58 1457 592 548 1443 162 1349 221 844 0\n1715 -163 -84 70 45 77 0 1709 1710 1706 1648 1604 1708 1471 1704 165 189 561 601 609 1457 1443 160 1064 552 56 57 58 63 1381 1496 593 592 614 548 1460 586 590 566 577 580 1615 1673 525 571 573 72 280 540 169 411 531 1714 204 535 1358 845 0\n1716 -78 -40 -42 -83 -59 -57 -18 -84 0 1709 1471 1704 280 411 169 71 387 72 1443 157 1350 224 846 0\n1717 -28 -40 -42 -83 -59 72 -57 -18 -84 0 1709 1712 1705 1704 280 411 169 72 71 1443 1394 1341 848 0\n1718 32 -13 28 -40 -42 -83 -159 -59 -57 -18 -84 0 1709 1704 1716 280 411 1443 1347 535 847 0\n1719 -84 70 45 77 0 1709 1710 1604 1708 1706 1648 1704 165 189 1443 561 601 1715 554 604 1438 618 1458 1460 593 595 586 590 1496 566 577 580 1615 1673 525 571 71 72 280 387 169 411 1320 531 151 548 1716 1717 1405 1718 221 849 0\n1720 14 -74 -20 -57 -175 -17 -40 0 1708 1604 1709 1471 1704 136 183 590 586 566 525 72 1615 1673 280 169 1320 1424 577 531 411 71 387 221 1410 209 851 0\n1721 -57 -164 -175 -17 -40 84 45 0 1708 1604 1709 1471 1704 183 590 586 566 525 72 1615 1673 280 169 1320 1424 155 577 531 411 580 571 61 1390 557 121 136 1720 850 209 535 851 0\n1722 78 -26 -89 -12 -42 -83 -159 -59 -17 -40 0 1709 1704 10 1 183 1424 280 411 1408 535 842 0\n1723 54 -40 70 45 77 0 1604 1708 1709 1471 1704 1719 1377 1077 183 145 47 1138 552 618 1458 1456 1460 593 597 586 590 566 577 580 1615 1673 525 571 71 72 280 387 169 411 1320 531 155 1424 1721 1072 1387 543 557 1722 224 840 0\n1724 -40 70 45 77 0 1471 1648 1719 25 1077 1723 55 59 63 175 543 593 1545 1458 1460 607 586 590 597 566 580 1639 1673 573 155 540 0\n1725 -80 83 40 0 1706 1648 1710 140 149 187 548 561 595 601 1458 609 604 614 1064 1460 586 590 566 580 1673 573 540 0\n1726 165 169 -184 33 80 84 70 45 0 1704 1648 618 607 563 564 601 597 1135 609 1639 614 1138 1079 595 1068 0\n1727 -177 -181 57 40 70 77 0 1471 1706 1648 1704 593 595 543 548 175 190 45 144 1138 0\n1728 -184 26 57 80 70 45 77 0 1706 1471 1724 1719 618 1727 614 609 599 1639 557 1656 178 543 0\n1729 -175 83 0 1604 1708 586 590 566 1615 525 72 280 169 1673 1320 0\n1730 57 83 70 45 77 0 1706 1471 1709 1710 1729 1460 618 1724 1725 1728 1727 55 614 1656 606 609 543 552 601 190 146 561 0\n1731 -59 78 -91 -74 -15 -3 -46 -171 -57 83 0 1648 1712 1713 1704 43 42 578 1729 1460 61 1487 72 73 181 280 1411 169 411 540 1397 1413 573 569 576 535 531 973 0\n1732 177 -57 83 40 84 70 45 0 1648 1710 1709 1708 1604 1704 545 176 63 61 1729 1460 1725 616 614 596 1459 606 609 549 588 552 599 601 1369 42 43 146 1419 557 561 1624 1731 525 275 566 585 1075 577 580 109 114 119 1411 1426 571 386 1519 535 269 531 875 0\n1733 59 -74 -17 -91 -5 -38 -57 70 0 1708 1604 1706 1709 1704 136 45 63 144 1152 620 1459 17 16 525 275 566 585 1657 577 580 109 114 119 1411 1426 571 386 1519 535 269 531 719 0\n1734 83 70 45 77 0 1706 1648 1713 1712 1704 1724 1719 1725 1729 1460 618 1730 61 63 1487 1732 595 548 16 17 45 144 1079 1375 1152 1138 604 620 1430 599 1459 557 588 136 578 1733 72 73 181 280 1411 169 411 540 1397 1414 573 569 576 535 531 972 0\n1735 -32 -42 -74 -59 -5 -17 -91 -57 -3 -83 0 1704 280 411 71 387 154 221 995 0\n1736 46 -91 -57 54 70 45 77 0 1706 1709 1648 1604 1708 1471 1704 61 1724 1734 151 548 595 1458 1371 156 155 154 1719 1420 552 1375 1657 604 1488 566 599 1460 1615 525 557 590 72 280 121 136 577 580 169 411 531 571 1735 209 535 839 0\n1737 -42 172 -74 -59 -46 -91 -57 -3 -83 0 1713 1471 1704 43 154 1397 280 411 169 542 533 581 574 538 209 1358 838 0\n1738 -164 -59 -46 -91 -57 -3 -83 84 45 0 1706 1711 1713 1604 1704 527 568 280 411 169 71 387 73 72 553 43 42 564 545 594 61 151 1672 1459 588 155 154 557 602 136 1397 610 615 1461 591 1737 1337 531 249 970 576 535 571 0\n1739 32 -159 -42 -18 -59 -46 -91 -57 -3 -83 0 1704 280 411 169 43 42 1347 535 1358 829 0\n1740 -59 -46 -91 -57 70 45 77 0 1648 1706 1704 1724 1734 151 548 595 1371 156 154 1719 71 72 73 280 387 169 411 1738 559 265 1616 614 1460 590 577 580 531 571 1739 1349 221 986 0\n1741 -86 -8 -42 -32 -14 -74 -7 -46 -91 -57 -3 -83 0 1704 411 856 0\n1742 90 -8 -42 -32 -14 -74 -7 -46 -91 -57 -3 -83 0 1707 1704 1741 277 1433 858 0\n1743 -8 -42 -83 -32 -14 -74 -7 -46 -91 -57 -3 0 1704 1742 413 873 0\n1744 -42 -32 -14 -74 59 -46 -91 -57 -3 -83 0 1604 1704 275 283 1743 0\n1745 -91 -57 54 70 45 77 0 1648 1706 1708 1604 1709 1704 545 176 1724 1734 151 548 595 1672 1459 1371 156 1736 42 43 1740 525 275 566 586 585 1460 577 580 614 571 1624 1616 1519 1410 535 8 9 387 1744 531 249 288 311 872 0\n1746 -57 54 70 45 77 0 1648 1710 1706 1713 1604 1708 1704 1724 1734 151 548 595 1458 607 1371 156 155 154 1719 61 1745 561 1389 1390 1138 601 597 42 43 1661 609 557 566 614 136 1397 1615 525 1460 72 280 590 169 411 577 580 531 571 978 535 0\n1747 91 54 70 45 77 0 1648 1706 1710 1471 1604 1708 1704 1746 1387 1724 1734 151 548 595 1458 607 1371 156 155 1719 561 1389 1138 601 597 42 43 609 1457 614 592 1460 543 586 590 178 566 577 580 557 1615 525 571 10 71 72 280 535 387 169 411 224 531 980 0\n1748 74 -42 -159 -59 -164 -46 -91 -12 54 -3 -83 84 45 0 1713 1704 280 411 169 72 71 43 42 155 557 1439 10 1340 535 984 0\n1749 54 70 45 77 0 1471 1648 1706 1708 1604 1713 1704 1724 1734 151 548 1371 156 154 1719 1746 1387 1747 190 543 1226 592 1460 1457 586 590 609 1152 566 577 580 599 42 43 1615 525 571 72 280 169 411 531 1748 136 267 1397 535 993 0\n1750 70 45 77 0 1471 1648 1706 1719 1724 1734 151 155 548 1749 63 175 1639 543 599 592 609 1457 0\n1751 74 -40 -42 -164 -159 -59 -17 -83 -70 45 0 1709 1713 1704 280 411 169 72 71 186 1424 155 177 161 105 100 99 557 1434 10 1340 535 854 0\n1752 45 77 0 1704 1713 1604 1648 1706 1708 1709 1750 99 100 101 104 105 106 161 186 1640 593 1656 1458 1460 607 586 590 1729 566 577 580 154 156 1420 1424 1615 525 571 1067 72 280 601 597 169 411 609 531 1457 592 548 1751 136 267 1397 535 853 0\n1753 54 -83 77 0 1648 1704 1471 1752 151 1069 595 1458 156 103 62 48 1152 1138 1457 190 592 543 0\n1754 -32 -83 77 0 1706 1710 1471 1648 1708 1604 1704 1752 38 151 159 62 1753 175 543 1545 1460 586 566 525 72 1615 590 577 280 169 531 411 71 387 156 1069 592 1457 609 601 561 41 1371 48 1420 154 123 1349 221 990 0\n1755 -83 77 0 1706 1648 1604 1708 1710 1471 1704 1752 159 62 48 41 38 151 156 1420 1371 1069 1753 56 57 175 543 1545 592 1460 1457 586 590 609 566 577 580 601 1615 525 571 561 72 280 169 411 531 1754 204 535 1358 833 0\n1756 77 0 1709 1648 1752 38 41 48 62 103 159 1755 1729 1460 618 1727 614 606 552 1620 58 1545 0\n1757 -28 0 1756 125 0\n1758 -46 0 1756 127 0\n1759 -57 0 1756 128 0\n1760 -74 0 1756 129 0\n1761 -78 0 1756 137 0\n1762 -82 0 1756 148 0\n1763 -84 0 1756 163 0\n1764 -89 0 1756 179 0\n1765 161 0 1756 546 0\n1766 176 0 1765 594 0\n1767 -59 -91 -54 83 0 1648 1706 1763 1712 1713 1757 1761 1756 1704 187 1729 1460 58 183 548 595 614 609 599 1639 1369 1425 1672 1459 588 578 59 57 72 73 181 280 1411 169 411 540 1398 1413 573 569 576 535 531 975 0\n1768 -91 -54 83 0 1706 1648 1763 1708 1604 1757 1761 1704 1756 58 1672 1459 57 1729 1460 183 187 1425 548 1369 595 614 609 599 1639 1767 525 275 566 585 1075 577 580 109 114 119 1411 1426 571 386 1519 535 269 531 869 0\n1769 59 -12 -80 -40 -20 -54 0 1706 1708 1604 1757 1761 1756 1704 58 1672 1459 57 525 275 566 585 1665 577 580 109 114 119 1411 1426 571 386 1519 535 269 531 705 0\n1770 -54 83 0 1762 1710 1706 1648 1763 1709 1759 1712 1713 1757 1761 1756 1704 1729 1460 618 607 57 58 59 105 554 1672 1459 588 578 1768 1428 561 601 597 609 614 595 1069 548 1630 1387 1769 72 73 181 280 1411 169 411 540 1398 1417 573 569 576 535 531 976 0\n1771 -59 91 83 0 1710 1648 1762 1758 1706 1712 1713 1757 1761 1604 1759 1763 1760 1756 1704 1729 1460 618 1770 1138 101 561 601 609 614 595 548 1672 1459 588 578 607 597 103 102 100 1406 72 73 181 280 1411 169 411 540 1398 1427 573 569 576 535 531 10 1346 557 819 0\n1772 91 83 0 1758 1762 1710 1706 1648 1708 1757 1761 1604 1759 1763 1760 1756 1704 1770 1406 1729 1460 618 607 1138 561 100 101 102 103 601 597 1672 609 1459 614 595 548 1771 525 275 566 585 577 580 571 573 1519 535 540 8 10 1346 112 114 1411 1426 531 557 1356 704 0\n1773 159 83 0 1762 1758 1648 1706 1772 183 1729 1460 1770 186 1152 614 595 548 22 620 1459 588 578 571 569 580 540 585 1673 566 0\n1774 169 83 0 1759 1762 1648 1706 1761 1757 1709 1758 1760 1763 1712 1713 1604 1708 1756 1704 1772 187 1729 1460 618 1770 186 552 604 599 183 1152 614 595 548 17 1773 535 10 557 9 387 1346 8 1519 620 1459 588 1406 580 574 576 585 541 566 1414 1398 1615 525 531 280 289 816 0\n1775 83 0 1709 1758 1762 1706 1648 1757 1761 1759 1763 1760 1604 1756 1704 1729 1460 618 1770 1406 1772 183 186 187 552 1152 604 620 614 599 1459 595 548 17 22 1773 1519 535 8 9 10 1346 387 557 1774 573 540 114 172 1411 1426 1673 280 291 566 275 706 585 531 577 0\n1776 -38 0 1775 151 0\n1777 -72 0 1775 154 0\n1778 -80 0 1775 155 0\n1779 160 0 1775 542 0\n1780 -185 0 1776 1706 1672 0\n1781 174 0 1780 1459 0\n1782 171 0 1781 588 0\n1783 42 -91 156 -32 0 1761 1604 1781 1759 1648 1776 1706 1760 1763 1778 1775 1756 1704 10 566 586 1460 183 548 595 614 609 599 557 1371 1074 585 577 527 275 11 1410 9 387 14 8 531 249 288 311 866 0\n1784 -90 -91 156 -32 0 1761 1604 1759 1648 1776 1706 1760 1763 1778 1775 1756 1704 527 1783 283 10 566 586 1460 183 548 595 614 609 599 557 1371 1074 275 11 1410 413 867 0\n1785 86 -91 156 -32 0 1761 1604 1759 1648 1776 1706 1760 1763 1778 1712 1775 1756 1704 1784 527 1783 283 10 566 586 1460 183 548 595 614 609 599 557 1371 1074 275 11 1410 277 1432 859 0\n1786 -91 156 -32 0 1761 1604 1759 1706 1776 1648 1778 1763 1760 1775 1756 1704 10 566 586 1460 1074 527 275 11 1410 183 1371 548 595 614 609 599 557 1783 283 1785 411 857 0\n1787 156 -32 0 1762 1710 1778 1763 1760 1776 1648 10 566 586 1460 618 607 1786 561 601 597 609 557 614 1069 595 0\n1788 -45 91 -32 0 1761 1708 1604 1709 1710 1776 1648 1758 1762 1775 1756 1704 561 601 609 1424 9 387 1787 525 289 280 1615 11 1410 14 8 103 1365 1069 1428 595 1458 614 1138 1460 979 590 531 577 0\n1789 -54 91 -32 0 1761 1708 1604 1709 1648 1776 1706 1760 1778 1762 1763 1710 1756 1704 1775 1787 1615 8 14 561 10 1788 557 597 607 618 1460 590 577 531 1458 595 548 1424 9 387 525 289 280 11 1410 1436 1381 843 0\n1790 91 -32 0 1761 1708 1762 1710 1778 1763 1760 1706 1776 1648 1604 1759 1758 1709 1775 1756 1704 9 387 1787 525 289 280 1615 11 1410 14 10 8 1424 561 1788 557 597 607 1456 618 1458 1460 595 590 548 577 531 1789 1406 1346 552 852 0\n1791 45 -32 0 1761 1708 1604 1648 1776 1706 1759 1778 1763 1760 1758 1709 1756 1704 1775 1790 183 548 595 1458 1371 186 9 387 1787 525 289 280 1615 11 1410 14 10 8 1392 557 1344 599 609 604 614 552 1460 989 590 531 577 0\n1792 42 -32 0 1761 1708 1706 1604 1756 1704 1759 1775 1791 1790 183 1371 9 387 1787 525 289 280 1615 11 1410 14 10 8 1337 531 249 577 971 590 1074 1460 0\n1793 -32 0 1761 1779 1711 1708 1706 1766 1604 1759 1775 1756 1704 9 11 538 387 1410 574 1787 568 525 280 289 1790 183 564 1371 1791 558 602 1792 533 581 591 1461 615 610 554 1406 1346 982 0\n1794 54 -42 -45 -91 0 1759 1762 1777 1758 1706 1709 1604 1708 1775 1756 1704 1757 1761 1793 118 1345 38 183 1371 186 1074 1406 1657 1380 1460 566 590 525 580 280 289 825 571 535 0\n1795 -42 -45 -91 0 1706 1757 1793 1781 1604 1708 1756 1704 1775 1761 1345 183 1371 118 1794 57 535 1354 571 580 585 566 525 280 289 834 1410 0\n1796 169 42 0 1782 1781 1604 1708 580 576 585 566 1615 525 72 280 531 169 0\n1797 -45 -91 0 1757 1761 1793 1759 1775 1762 1777 1758 1706 1709 186 38 1795 1796 571 1519 535 3 57 1074 1657 1460 566 590 1615 577 531 0\n1798 42 -91 0 1648 1776 1757 1761 1793 1777 1706 1709 1758 1762 183 548 595 186 1796 571 1519 535 3 57 1657 1152 566 614 1615 1460 531 590 577 0\n1799 -30 -91 0 1648 1776 1759 1471 1762 1777 1758 1706 1709 1604 1708 1778 1763 1760 1775 1756 1704 1798 118 183 1371 1797 1361 1392 548 595 1458 186 57 1228 1406 1657 604 566 599 525 557 280 289 985 0\n1800 -91 0 1706 1759 1758 1471 1775 1761 1793 183 1371 417 1797 1392 1361 426 419 474 438 442 1798 1799 1410 1354 428 416 478 435 479 447 485 472 513 1451 0\n1801 19 0 1800 1775 1709 1424 0\n1802 -165 0 1800 1710 1762 561 0\n1803 -179 0 1802 601 0\n1804 -182 0 1803 609 0\n1805 159 -59 -42 0 1761 1793 1804 1706 1776 1648 1760 1778 1763 1802 1764 1775 1756 1704 1801 118 289 280 35 537 571 1410 1354 580 590 1460 618 614 607 595 597 548 1069 557 1726 264 855 0\n1806 -59 -42 0 1757 1761 1793 1758 1762 1800 1648 1802 1759 1778 1763 1760 1775 1756 1704 1801 118 280 289 1805 535 57 100 1228 1406 1428 1138 1456 1243 597 41 1374 557 841 0\n1807 167 0 1781 1803 1757 1761 1793 1758 586 585 1460 580 618 571 604 535 57 1228 0\n1808 156 0 1807 566 0\n1809 -53 0 1808 1615 0\n1810 59 0 1808 1708 1604 525 0\n1811 -33 0 1810 72 0\n1812 86 0 1810 280 0\n1813 -42 0 1810 1806 0\n1814 -23 0 1812 169 0\n1815 169 0 1813 1796 0\n1816 -158 0 1814 1809 1811 1813 531 0\n1817 159 0 1815 571 0\n1818 -172 0 1816 577 0\n1819 30 0 1817 1793 1761 1757 535 0\n1820 -175 0 1818 590 0\n1821 -54 0 1819 57 0\n1822 -70 0 1819 100 0\n1823 184 0 1820 1460 0\n1824 -181 0 1822 1800 1762 1821 1758 1704 1138 0\n1825 0 1823 1824 618 0\n"

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

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "338c70dc8f32a3693a358b6c38ce8b86e4789e17b31ca719366394e715356352d70d934cd1b61d4749d1772364cd34ccb3c2d4b32e2b4ac6b26c5bc1e2729c6745c5783d0f23e2c0f11a0e8c6258361382e07b098a5190e4c5894950d60d1342d074c344c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db4da49a4924d2693492492493492492492692492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 17
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
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)])))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.leaf ([(facetIndex 18)])))
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.leaf ([(facetIndex 20)]))))
 (.branch 23
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)])))
 (.branch 24
 (.leaf ([(facetIndex 23)]))
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.leaf ([(facetIndex 25)]))))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ([(facetIndex 26)]))
 (.leaf ([(facetIndex 27)])))
 (.branch 29
 (.leaf ([(facetIndex 28)]))
 (.leaf ([(facetIndex 29)]))))
 (.branch 32
 (.branch 31
 (.leaf ([(facetIndex 30)]))
 (.leaf ([(facetIndex 31)])))
 (.branch 33
 (.leaf ([(facetIndex 32)]))
 (.branch 34
 (.leaf ([(facetIndex 33)]))
 (.leaf ([(facetIndex 34)]))))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨6, sparse_nat% "228607de75c6da6585d65544d24503ce34c2ca2481c61440c2040"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 35
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 44), (facetIndex 45), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 60), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 82), (facetIndex 83)]))
 (.branch 4
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 84)]))
 (.leaf ([(facetIndex 37), (facetIndex 42), (facetIndex 48), (facetIndex 51), (facetIndex 79)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 46), (facetIndex 47), (facetIndex 49), (facetIndex 50)]))
 (.branch 7
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 61), (facetIndex 63), (facetIndex 64)]))
 (.leaf ([(facetIndex 58), (facetIndex 62), (facetIndex 67)]))))
 (.branch 9
 (.leaf ([(facetIndex 40), (facetIndex 78), (facetIndex 80)]))
 (.branch 10
 (.leaf ([(facetIndex 65)]))
 (.leaf ([(facetIndex 69), (facetIndex 73)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10032208483330a101a0719667616760000045545500042800455z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 71)]))
 (.branch 2
 (.leaf ([(facetIndex 85)]))
 (.leaf ([(facetIndex 88)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 43), (facetIndex 56)]))
 (.leaf ([(facetIndex 68), (facetIndex 74)])))
 (.branch 6
 (.leaf ([(facetIndex 81), (facetIndex 86)]))
 (.leaf ([(facetIndex 89), (facetIndex 90)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b21480280001000040000000030000000006z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1]
def grouped1_0002 : List Nat := [0, 1, 2, 3]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0004 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def grouped1_0006 : List Nat := [1]
def grouped1_0007 : List Nat := [2, 3]
def grouped1_0008 : List Nat := [4]
def grouped1_0009 : List Nat := [4, 5]
def grouped1_0010 : List Nat := [4, 5, 6, 7]
def grouped1_0011 : List Nat := [5]
def grouped1_0012 : List Nat := [6]
def grouped1_0013 : List Nat := [6, 7]
def grouped1_0014 : List Nat := [7]
def grouped1_0015 : List Nat := [8]
def grouped1_0016 : List Nat := [8, 9]
def grouped1_0017 : List Nat := [8, 9, 10, 11]
def grouped1_0018 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15, 16]
def grouped1_0019 : List Nat := [9]
def grouped1_0020 : List Nat := [10]
def grouped1_0021 : List Nat := [10, 11]
def grouped1_0022 : List Nat := [11]
def grouped1_0023 : List Nat := [12]
def grouped1_0024 : List Nat := [12, 13]
def grouped1_0025 : List Nat := [12, 13, 14, 15, 16]
def grouped1_0026 : List Nat := [13]
def grouped1_0027 : List Nat := [14]
def grouped1_0028 : List Nat := [14, 15, 16]
def grouped1_0029 : List Nat := [15]
def grouped1_0030 : List Nat := [15, 16]
def grouped1_0031 : List Nat := [16]
def grouped1_0032 : List Nat := [17]
def grouped1_0033 : List Nat := [17, 18]
def grouped1_0034 : List Nat := [17, 18, 19, 20]
def grouped1_0035 : List Nat := [17, 18, 19, 20, 21, 22, 23, 24, 25]
def grouped1_0036 : List Nat := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
def grouped1_0037 : List Nat := [18]
def grouped1_0038 : List Nat := [19]
def grouped1_0039 : List Nat := [19, 20]
def grouped1_0040 : List Nat := [20]
def grouped1_0041 : List Nat := [21, 22, 23, 24, 25]
def grouped1_0042 : List Nat := [26, 27, 28, 29]
def grouped1_0043 : List Nat := [26, 27, 28, 29, 30, 31, 32, 33, 34]
def grouped1_0044 : List Nat := [30, 31]
def grouped1_0045 : List Nat := [30, 31, 32, 33, 34]
def grouped1_0046 : List Nat := [32]
def grouped1_0047 : List Nat := [32, 33, 34]
def grouped1_0048 : List Nat := [33]
def grouped1_0049 : List Nat := [33, 34]
def grouped1_0050 : List Nat := [34]
def grouped2_0051 : List Nat := [0]
def grouped2_0052 : List Nat := [0, 1]
def grouped2_0053 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0055 : List Nat := [1]
def grouped2_0056 : List Nat := [2]
def grouped2_0057 : List Nat := [2, 3, 4]
def grouped2_0058 : List Nat := [3]
def grouped2_0059 : List Nat := [3, 4]
def grouped2_0060 : List Nat := [4]
def grouped2_0061 : List Nat := [5]
def grouped2_0062 : List Nat := [5, 6, 7]
def grouped2_0063 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0064 : List Nat := [6]
def grouped2_0065 : List Nat := [6, 7]
def grouped2_0066 : List Nat := [7]
def grouped2_0067 : List Nat := [8]
def grouped2_0068 : List Nat := [8, 9, 10]
def grouped2_0069 : List Nat := [9]
def grouped2_0070 : List Nat := [9, 10]
def grouped2_0071 : List Nat := [10]
def grouped3_0072 : List Nat := [0]
def grouped3_0073 : List Nat := [0, 1, 2]
def grouped3_0075 : List Nat := [1]
def grouped3_0076 : List Nat := [1, 2]
def grouped3_0077 : List Nat := [2]
def grouped3_0078 : List Nat := [3]
def grouped3_0079 : List Nat := [3, 4]
def grouped3_0080 : List Nat := [3, 4, 5, 6]
def grouped3_0081 : List Nat := [4]
def grouped3_0082 : List Nat := [5]
def grouped3_0083 : List Nat := [5, 6]
def grouped3_0084 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":32},{\"tag\":\"group\",\"kind\":1,\"index\":34},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0030\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0049\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0047\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0047\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0045\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0045\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0043\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0043\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0057\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0057\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0057\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0065\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0065\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0070\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0070\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0068\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0068\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0068\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0063\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0063\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0063\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0063\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0076\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0073\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0079\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0079\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0083\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0083\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0080\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0080\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record001" 194

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record001" "{\"ridges\":[[0,11],[1,21],[2,7],[2,35],[2,37],[3,69],[6,11],[6,35],[6,41],[7,11],[7,67],[7,74],[8,11],[8,266],[9,19],[9,50],[10,19],[10,145],[11,19],[11,273],[11,274],[12,131],[13,21],[13,25],[14,37],[14,41],[15,13],[15,73],[15,76],[17,21],[17,37],[18,21],[18,145],[19,37],[19,517],[20,193],[21,41],[21,49],[22,273],[23,545],[23,552],[24,776],[26,14],[27,14],[27,70],[27,74],[29,146],[30,194],[32,266],[32,274],[32,280],[33,44],[34,44],[34,524],[35,11],[35,13],[40,35],[40,37],[40,69],[40,70],[41,35],[41,37],[41,131],[42,35],[42,517],[42,545],[42,548],[43,517],[43,774],[44,74],[46,74],[48,35],[49,11],[49,131],[50,67],[50,74],[50,259],[50,266],[51,769],[51,776],[54,19],[55,131],[55,145],[55,259],[55,273],[56,35],[56,802],[57,21],[57,25],[57,76],[59,273],[59,280],[61,37],[61,41],[61,44],[61,76],[62,13],[62,193],[63,69],[63,73],[63,76],[63,517],[63,524],[64,517],[64,769],[64,776],[65,37],[67,21],[67,69],[67,145],[68,21],[68,273],[68,517],[68,788],[69,273],[69,280],[70,552],[72,776],[73,41],[73,545],[73,769],[73,776],[74,273],[74,816],[75,74],[76,14],[76,146],[77,266],[78,74],[79,38],[79,524],[79,552],[80,14],[80,74],[80,194],[81,14],[81,266],[81,524],[81,774],[82,38],[82,50],[82,52],[82,146],[82,148],[83,70],[83,146],[84,50],[84,266],[86,266],[86,802],[87,524],[89,28],[89,280],[89,524],[89,788],[90,280],[90,816]],\"owners\":[[2,7,[0,1,3,4,36,37,39,43],[42]],[7,11,[0,5,6,8,35,37,45,48,51],[49]],[8,11,[0,5,6,7,35,37,45,48,49],[51]],[15,13,[0,13,14,16,35,36,58,59,64],[62]],[35,13,[13,14,15,16,59,64],[0,36,58,62]],[62,13,[0,13,14,16,36,59,64],[15,35,58]],[67,21,[1,13,17,39,59,60,66,68],[18,38,57]],[2,35,[6,9,46,47,48,52,53,56],[40,41,42]],[40,35,[6,9,47,48,52,53,56],[2,41,42,46]],[41,35,[6,9,46,47,48,53,56],[2,40,42,52]],[42,35,[6,9,46,47,52,53],[2,40,41,48,56]],[48,35,[2,9,40,41,52,53],[6,42,46,47,56]],[19,37,[2,14,17,40,41,61,65],[]],[79,38,[2,28,40,41,82],[26,42,78]],[82,38,[2,26,40,42,78,79],[28,41]],[7,67,[3,12,38,40,54],[44,46,50]],[50,67,[3,12,38,40,54],[7,44,46]],[49,131,[4,10,41,52,55],[12,35,45]],[13,25,[5,21,22,44,45,70,71,72],[57,58,60]],[57,25,[5,21,22,45,70,72],[13,44,58,60,71]],[73,41,[6,14,21,46,61],[23,47,69]],[15,73,[7,44,46,49,50,71],[57,61,62,63]],[63,73,[7,44,46,49,50,71],[15,57,61,62]],[7,74,[27,75,78,80,85],[44,46,49,50]],[27,74,[7,44,46,49,50,85],[75,78,80]],[44,74,[27,78,80],[7,46,49,50,75,85]],[46,74,[27,75,80,85],[7,44,49,50,78]],[50,74,[27,75,78,80,85],[7,44,46,49]],[75,74,[7,46,49,50],[27,44,78,80,85]],[78,74,[7,44,49,50,85],[27,46,75,80]],[80,74,[7,44,46,50],[27,49,75,78,85]],[50,259,[11,39,43,53,55,56],[8,36,47,51]],[55,259,[8,36,43,47,50,51,56],[11,39,53]],[8,266,[32,77,81,84,86],[36,47,50,51]],[32,266,[8,36,47,50,51,81,86],[77,84]],[50,266,[32,77,81,84,86],[8,36,47,51]],[21,49,[9,17,52,53,65,66,74],[69,70]],[10,145,[18,58,65,67,71],[45,52,54,55]],[18,145,[10,45,52,54,55,71],[58,65,67]],[55,145,[18,58,65,67,71],[10,45,52,54]],[67,145,[10,45,52,55],[18,54,58,65,71]],[29,146,[10,45,52,54,55,85],[76,82,83]],[76,146,[10,52,54,55],[29,45,82,83,85]],[82,146,[10,45,54,55,85],[29,52,76,83]],[83,146,[10,45,52,55],[29,54,76,82,85]],[11,274,[32,77,84],[39,53,55]],[32,274,[11,39,53,55],[77,84]],[20,193,[12,49,54,71],[62,67]],[62,193,[12,54],[20,49,67,71]],[30,194,[12,49,54,85],[80,83]],[80,194,[12,54],[30,49,83,85]],[89,28,[13,25,33,57,58,75,76,88],[59,60,77,87]],[15,76,[27,75,78,80,88],[57,61,62,63]],[57,76,[27,78,80],[15,61,62,63,75,88]],[61,76,[27,75,80,88],[15,57,62,63,78]],[63,76,[27,75,78,80,88],[15,57,61,62]],[19,517,[16,37,43,60,63,64,68],[42,66]],[42,517,[16,60,63,64,68],[19,37,43,66]],[63,517,[19,42,43,66,68],[16,37,60,64]],[64,517,[19,42,66],[16,37,43,60,63,68]],[68,517,[16,19,37,42,63],[43,60,64,66]],[34,524,[16,37,60,63,64,81,89],[79,87]],[79,524,[16,60,63,64,89],[34,37,81,87]],[87,524,[16,37,63,64,81],[34,60,79,89]],[89,524,[16,34,37,63,79],[60,64,81,87]],[82,52,[17,33,66,87],[28,65]],[82,148,[18,58,67,88],[29,65,76,83]],[23,545,[19,42,56,66,74],[48,70,73]],[42,545,[23,70,73,74],[19,48,56,66]],[73,545,[19,42,66],[23,48,56,70,74]],[42,548,[34,87],[19,66,79]],[23,552,[34,79,86,87,90],[48,70,73]],[70,552,[34,79,86],[23,48,73,87,90]],[79,552,[23,70,73,90],[34,48,86,87]],[51,769,[68,74],[24,43,56,64,72,73]],[64,769,[56,74],[24,43,51,68,72,73]],[73,769,[43,68],[24,51,56,64,72,74]],[24,776,[81,86,89,90],[51,64,72,73]],[51,776,[89,90],[24,64,72,73,81,86]],[64,776,[86,90],[24,51,72,73,81,89]],[72,776,[81,86],[24,51,64,73,89,90]],[73,776,[81,89],[24,51,64,72,86,90]],[43,774,[81],[]],[81,774,[43],[]],[56,802,[86],[]],[86,802,[56],[]],[68,788,[89],[]],[89,788,[68],[]],[74,816,[90],[]],[90,816,[74],[]]],\"edges\":[[15,[8,11,32,36,39,43,47,50,51,53,55,56,77,81,84,86]],[20,[3,15,20,27,30,38,40,57,61,62,63,67,75,78,80,83,88]],[23,[16,19,34,37,42,43,60,63,64,66,68,79,81,87,89]],[26,[7,15,27,44,46,49,50,57,61,62,63,71,75,78,80,85,88]],[32,[10,18,29,45,52,54,55,58,65,67,71,76,82,83,85,88]],[38,[19,23,34,42,48,56,66,70,73,74,79,86,87,90]],[44,[24,43,51,56,64,68,72,73,74,81,86,89,90]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-40,-1],[-40,-35],[-41,-4],[-41,-37],[-41,-40],[-42,-41],[-43,-35],[-43,-36],[-43,-40],[-43,-41],[-45,-12],[-46,-9],[-46,-40],[-49,-40],[-50,-7],[-50,-44],[-50,-45],[-50,-46],[-52,-12],[-54,-41],[-55,-6],[-55,-10],[-55,-38],[-55,-44],[-55,-45],[-55,-52],[-55,-54],[-57,-17],[-57,-37],[-57,-54],[-59,-36],[-59,-39],[-59,-43],[-59,-51],[-61,-14],[-61,-17],[-61,-37],[-61,-40],[-61,-42],[-61,-46],[-61,-60],[-62,-40],[-62,-57],[-62,-61],[-63,-1],[-63,-37],[-63,-58],[-63,-61],[-63,-62],[-64,-24],[-64,-37],[-64,-48],[-64,-51],[-64,-60],[-65,-41],[-65,-42],[-65,-58],[-65,-59],[-66,-3],[-66,-41],[-66,-65],[-67,-5],[-67,-38],[-67,-41],[-67,-54],[-67,-57],[-67,-65],[-68,-36],[-68,-39],[-68,-58],[-68,-59],[-68,-60],[-68,-64],[-68,-65],[-68,-66],[-69,-47],[-69,-48],[-69,-51],[-69,-53],[-69,-56],[-69,-60],[-70,-46],[-70,-64],[-70,-68],[-70,-69],[-71,-58],[-71,-62],[-71,-67],[-72,-64],[-72,-69],[-73,-17],[-73,-37],[-73,-47],[-73,-48],[-73,-51],[-73,-53],[-73,-60],[-73,-63],[-73,-64],[-73,-70],[-73,-72],[-74,-47],[-74,-53],[-74,-60],[-74,-66],[-74,-68],[-74,-69],[-74,-70],[-74,-73],[-75,-67],[-76,-29],[-76,-49],[-76,-62],[-77,-6],[-77,-43],[-77,-44],[-77,-45],[-77,-59],[-77,-64],[-77,-68],[-77,-75],[-78,-75],[-78,-76],[-78,-77],[-79,-15],[-79,-33],[-79,-61],[-79,-75],[-79,-78],[-80,-40],[-80,-49],[-80,-58],[-80,-62],[-80,-71],[-80,-76],[-81,-37],[-81,-42],[-81,-48],[-81,-56],[-81,-59],[-81,-64],[-81,-75],[-81,-77],[-81,-78],[-81,-79],[-82,-2],[-82,-26],[-82,-39],[-82,-41],[-82,-52],[-82,-65],[-82,-75],[-82,-76],[-82,-77],[-83,-41],[-83,-57],[-83,-67],[-83,-71],[-83,-75],[-83,-76],[-83,-80],[-84,-47],[-84,-53],[-84,-56],[-84,-69],[-84,-73],[-84,-74],[-85,-58],[-85,-62],[-85,-67],[-85,-80],[-85,-83],[-86,-37],[-86,-42],[-86,-48],[-86,-69],[-86,-79],[-86,-81],[-86,-84],[-87,-68],[-87,-74],[-87,-78],[-87,-79],[-88,-58],[-88,-62],[-88,-67],[-88,-80],[-88,-83],[-90,-68],[-3,1,2,4,5,36,37,39,43],[-8,1,6,7,9,35,37,45,48,51],[-9,1,6,7,8,35,37,45,48,49],[-1,-7,-9],[-7,-8,-9],[-7,-9,-35],[-7,-9,-49],[-16,1,14,15,17,35,36,58,59,64],[-35,14,15,16,17,59,64],[-62,1,14,15,17,36,59,64],[-27,-80,-81],[-28,-76,-81],[-10,-11,-12],[-10,-12,-54],[-67,2,14,18,39,59,60,66,68],[-2,-67,-68],[-14,-19,-68],[-18,-19,-68],[-18,-67,-68],[-19,-57,-68],[-3,7,10,46,47,48,52,53,56],[-40,7,10,47,48,52,53,56],[-41,7,10,46,47,48,53,56],[-42,7,10,46,47,52,53],[-48,3,10,40,41,52,53],[-7,-40,-56],[-20,3,15,18,40,41,61,65],[-3,-18,-61],[-3,-20,-65],[-15,-20,-41],[-18,-20,-41],[-20,-40,-65],[-20,-41,-61],[-79,3,29,40,41,82],[-82,3,27,40,42,78,79],[-8,4,13,38,40,54],[-50,4,13,38,40,54],[-4,-63,-67],[-40,-63,-67],[-28,-40,-83],[-49,5,11,41,52,55],[-13,-41,-55],[-41,-49,-55],[-14,6,22,23,44,45,70,71,72],[-57,6,22,23,45,70,72],[-73,7,15,22,46,61],[-7,-15,-73],[-7,-22,-73],[-7,-61,-73],[-16,8,44,46,49,50,71],[-63,8,44,46,49,50,71],[-8,28,75,78,80,85],[-28,8,44,46,49,50,85],[-44,28,78,80],[-46,28,75,80,85],[-50,28,75,78,80,85],[-75,8,46,49,50],[-78,8,44,49,50,85],[-80,8,44,46,50],[-50,12,39,43,53,55,56],[-55,9,36,43,47,50,51,56],[-9,32,77,81,84,86],[-32,9,36,47,50,51,81,86],[-50,32,77,81,84,86],[-9,-77,-86],[-50,-77,-86],[-50,-81,-84],[-22,10,18,52,53,65,66,74],[-10,-82,-84],[-11,19,58,65,67,71],[-19,11,45,52,54,55,71],[-55,19,58,65,67,71],[-67,11,45,52,55],[-30,11,45,52,54,55,85],[-76,11,52,54,55],[-82,11,45,54,55,85],[-83,11,45,52,55],[-12,-59,-74],[-12,-68,-69],[-23,-55,-68],[-55,-59,-74],[-55,-68,-69],[-12,32,77,84],[-32,12,39,53,55],[-21,13,49,54,71],[-62,13,54],[-31,13,49,54,85],[-80,13,54],[-89,14,26,33,57,58,75,76,88],[-33,-34,-61],[-16,28,75,78,80,88],[-57,28,78,80],[-61,28,75,80,88],[-63,28,75,78,80,88],[-20,17,37,43,60,63,64,68],[-42,17,60,63,64,68],[-63,20,42,43,66,68],[-64,20,42,66],[-68,17,20,37,42,63],[-20,-43,-63],[-20,-63,-68],[-42,-63,-68],[-34,17,37,60,63,64,81,89],[-79,17,60,63,64,89],[-87,17,37,63,64,81],[-89,17,34,37,63,79],[-34,-63,-81],[-34,-63,-89],[-63,-81,-87],[-82,18,33,66,87],[-82,19,58,67,88],[-24,20,42,56,66,74],[-42,24,70,73,74],[-73,20,42,66],[-42,34,87],[-32,-59,-90],[-32,-69,-89],[-24,34,79,86,87,90],[-70,34,79,86],[-79,24,70,73,90],[-51,68,74],[-64,56,74],[-73,43,68],[-25,81,86,89,90],[-51,89,90],[-64,86,90],[-72,81,86],[-73,81,89],[-43,81],[-81,43],[-56,86],[-86,56],[-68,89],[-89,68],[-74,90],[-90,74],[-1,91],[-5,92],[-6,93],[-7,94],[-8,95],[-9,96],[-10,97],[-11,98],[-12,99],[-14,100],[-15,101],[-16,102],[-19,103],[-20,104],[-32,105],[-34,106],[-91,107],[-107,108],[-93,109],[-92,109],[-95,110],[-94,110],[-110,111],[-109,111],[-111,112],[-108,112],[-96,113],[-96,-97,114],[-99,115],[-98,-99,116],[-116,117],[-113,-115,117],[-113,-116,118],[-114,-115,118],[-100,119],[-102,120],[-120,121],[-101,121],[-121,122],[-119,122],[-117,123],[-117,-122,124],[-118,124],[-123,125],[-124,126],[-112,-123,126],[-103,127],[-104,128],[-128,129],[-127,-128,130],[-129,131],[-130,132],[-106,133],[-105,134],[-105,-133,135],[-134,136],[-135,137],[-136,138],[-137,139],[-139,140],[-131,-138,140],[-132,-138,141],[-125,-141,142],[-126,-140,142],[-142],[-143,38,39,44,45,52,53,54,55],[-144,60,66,70,72,87],[-145,41,82,83],[-146,75,76,77,84],[-147,37,42,48,51,79],[-37,147],[-42,147],[-48,147],[-79,147],[-148,35,36,46,47,49,50],[-149,57,59,61,63,64],[-150,58,62,67],[-151,40,78,80],[-152,65],[-65,152],[-153,69,73],[-73,153],[-154,143,144],[-155,144],[-156,146,147],[-157,146],[-157,147],[-158,145,156],[-159,145,157],[-160,145],[-159,156],[-160,157],[-161,154,160],[-161,155,159],[-162,155,160],[-163,155],[-161,158],[-162,159],[-163,160],[-164,149,150],[-165,149],[-165,150],[-167,148],[-166,164],[-167,165],[-168,152,153],[-169,152],[-169,153],[-152,-153,169],[-170,151,168],[-171,151,169],[-172,151],[-171,168],[-172,169],[-174,166,172],[-173,167,170],[-174,167,171],[-175,167,172],[-176,167],[-174,170],[-175,171],[-176,172],[-177,161,176],[-177,162,175],[-177,163,174],[-177,173],[177],[-178,71],[-71,178],[-179,85],[-85,179],[-180,88],[-88,180],[-181,43,56],[-56,181],[-182,68,74],[-68,182],[-74,182],[-183,81,86],[-81,183],[-86,183],[-184,89,90],[-89,184],[-90,184],[-185,179,180],[-180,185],[-179,185],[-186,178,185],[-185,186],[-178,186],[-187,181,182],[-182,187],[-181,187],[-188,182],[-189,183,184],[-184,189],[-183,189],[-190,184],[-183,-184,190],[-191,187,190],[-191,188,189],[-187,-189,191],[-187,-190,192],[-193,186,191],[-192,194],[-186,-191,194],[193],[-194],[9,12,32,36,39,43,47,50,51,53,55,56,77,81,84,86],[4,16,21,28,31,38,40,57,61,62,63,67,75,78,80,83,88],[17,20,34,37,42,43,60,63,64,66,68,79,81,87,89],[8,16,28,44,46,49,50,57,61,62,63,71,75,78,80,85,88],[11,19,30,45,52,54,55,58,65,67,71,76,82,83,85,88],[20,24,34,42,48,56,66,70,73,74,79,86,87,90],[25,43,51,56,64,68,72,73,74,81,86,89,90]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":32,\"kind\":1},{\"tag\":\"group\",\"index\":34,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":0},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":3},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":11},{\"tag\":\"incompatible\",\"a\":46,\"b\":8},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":49,\"b\":40},{\"tag\":\"incompatible\",\"a\":50,\"b\":6},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":11},{\"tag\":\"incompatible\",\"a\":54,\"b\":41},{\"tag\":\"incompatible\",\"a\":55,\"b\":5},{\"tag\":\"incompatible\",\"a\":55,\"b\":9},{\"tag\":\"incompatible\",\"a\":55,\"b\":38},{\"tag\":\"incompatible\",\"a\":55,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":16},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":36},{\"tag\":\"incompatible\",\"a\":59,\"b\":39},{\"tag\":\"incompatible\",\"a\":59,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":51},{\"tag\":\"incompatible\",\"a\":61,\"b\":13},{\"tag\":\"incompatible\",\"a\":61,\"b\":16},{\"tag\":\"incompatible\",\"a\":61,\"b\":37},{\"tag\":\"incompatible\",\"a\":61,\"b\":40},{\"tag\":\"incompatible\",\"a\":61,\"b\":42},{\"tag\":\"incompatible\",\"a\":61,\"b\":46},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":40},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":0},{\"tag\":\"incompatible\",\"a\":63,\"b\":37},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":23},{\"tag\":\"incompatible\",\"a\":64,\"b\":37},{\"tag\":\"incompatible\",\"a\":64,\"b\":48},{\"tag\":\"incompatible\",\"a\":64,\"b\":51},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":41},{\"tag\":\"incompatible\",\"a\":65,\"b\":42},{\"tag\":\"incompatible\",\"a\":65,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":66,\"b\":2},{\"tag\":\"incompatible\",\"a\":66,\"b\":41},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":4},{\"tag\":\"incompatible\",\"a\":67,\"b\":38},{\"tag\":\"incompatible\",\"a\":67,\"b\":41},{\"tag\":\"incompatible\",\"a\":67,\"b\":54},{\"tag\":\"incompatible\",\"a\":67,\"b\":57},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":36},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":58},{\"tag\":\"incompatible\",\"a\":68,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":47},{\"tag\":\"incompatible\",\"a\":69,\"b\":48},{\"tag\":\"incompatible\",\"a\":69,\"b\":51},{\"tag\":\"incompatible\",\"a\":69,\"b\":53},{\"tag\":\"incompatible\",\"a\":69,\"b\":56},{\"tag\":\"incompatible\",\"a\":69,\"b\":60},{\"tag\":\"incompatible\",\"a\":70,\"b\":46},{\"tag\":\"incompatible\",\"a\":70,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":58},{\"tag\":\"incompatible\",\"a\":71,\"b\":62},{\"tag\":\"incompatible\",\"a\":71,\"b\":67},{\"tag\":\"incompatible\",\"a\":72,\"b\":64},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":16},{\"tag\":\"incompatible\",\"a\":73,\"b\":37},{\"tag\":\"incompatible\",\"a\":73,\"b\":47},{\"tag\":\"incompatible\",\"a\":73,\"b\":48},{\"tag\":\"incompatible\",\"a\":73,\"b\":51},{\"tag\":\"incompatible\",\"a\":73,\"b\":53},{\"tag\":\"incompatible\",\"a\":73,\"b\":60},{\"tag\":\"incompatible\",\"a\":73,\"b\":63},{\"tag\":\"incompatible\",\"a\":73,\"b\":64},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":47},{\"tag\":\"incompatible\",\"a\":74,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":60},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":67},{\"tag\":\"incompatible\",\"a\":76,\"b\":28},{\"tag\":\"incompatible\",\"a\":76,\"b\":49},{\"tag\":\"incompatible\",\"a\":76,\"b\":62},{\"tag\":\"incompatible\",\"a\":77,\"b\":5},{\"tag\":\"incompatible\",\"a\":77,\"b\":43},{\"tag\":\"incompatible\",\"a\":77,\"b\":44},{\"tag\":\"incompatible\",\"a\":77,\"b\":45},{\"tag\":\"incompatible\",\"a\":77,\"b\":59},{\"tag\":\"incompatible\",\"a\":77,\"b\":64},{\"tag\":\"incompatible\",\"a\":77,\"b\":68},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":14},{\"tag\":\"incompatible\",\"a\":79,\"b\":33},{\"tag\":\"incompatible\",\"a\":79,\"b\":61},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":40},{\"tag\":\"incompatible\",\"a\":80,\"b\":49},{\"tag\":\"incompatible\",\"a\":80,\"b\":58},{\"tag\":\"incompatible\",\"a\":80,\"b\":62},{\"tag\":\"incompatible\",\"a\":80,\"b\":71},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":37},{\"tag\":\"incompatible\",\"a\":81,\"b\":42},{\"tag\":\"incompatible\",\"a\":81,\"b\":48},{\"tag\":\"incompatible\",\"a\":81,\"b\":56},{\"tag\":\"incompatible\",\"a\":81,\"b\":59},{\"tag\":\"incompatible\",\"a\":81,\"b\":64},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":1},{\"tag\":\"incompatible\",\"a\":82,\"b\":25},{\"tag\":\"incompatible\",\"a\":82,\"b\":39},{\"tag\":\"incompatible\",\"a\":82,\"b\":41},{\"tag\":\"incompatible\",\"a\":82,\"b\":52},{\"tag\":\"incompatible\",\"a\":82,\"b\":65},{\"tag\":\"incompatible\",\"a\":82,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":76},{\"tag\":\"incompatible\",\"a\":82,\"b\":77},{\"tag\":\"incompatible\",\"a\":83,\"b\":41},{\"tag\":\"incompatible\",\"a\":83,\"b\":57},{\"tag\":\"incompatible\",\"a\":83,\"b\":67},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":80},{\"tag\":\"incompatible\",\"a\":84,\"b\":47},{\"tag\":\"incompatible\",\"a\":84,\"b\":53},{\"tag\":\"incompatible\",\"a\":84,\"b\":56},{\"tag\":\"incompatible\",\"a\":84,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":74},{\"tag\":\"incompatible\",\"a\":85,\"b\":58},{\"tag\":\"incompatible\",\"a\":85,\"b\":62},{\"tag\":\"incompatible\",\"a\":85,\"b\":67},{\"tag\":\"incompatible\",\"a\":85,\"b\":80},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":37},{\"tag\":\"incompatible\",\"a\":86,\"b\":42},{\"tag\":\"incompatible\",\"a\":86,\"b\":48},{\"tag\":\"incompatible\",\"a\":86,\"b\":69},{\"tag\":\"incompatible\",\"a\":86,\"b\":79},{\"tag\":\"incompatible\",\"a\":86,\"b\":81},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":68},{\"tag\":\"incompatible\",\"a\":87,\"b\":74},{\"tag\":\"incompatible\",\"a\":87,\"b\":78},{\"tag\":\"incompatible\",\"a\":87,\"b\":79},{\"tag\":\"incompatible\",\"a\":88,\"b\":58},{\"tag\":\"incompatible\",\"a\":88,\"b\":62},{\"tag\":\"incompatible\",\"a\":88,\"b\":67},{\"tag\":\"incompatible\",\"a\":88,\"b\":80},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":68},{\"tag\":\"mate\",\"ridge\":7,\"a\":2,\"owners\":[0,1,3,4,36,37,39,43]},{\"tag\":\"mate\",\"ridge\":11,\"a\":7,\"owners\":[0,5,6,8,35,37,45,48,51]},{\"tag\":\"mate\",\"ridge\":11,\"a\":8,\"owners\":[0,5,6,7,35,37,45,48,49]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[0,6,8]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[6,7,8]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[6,8,35]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[6,8,49]},{\"tag\":\"mate\",\"ridge\":13,\"a\":15,\"owners\":[0,13,14,16,35,36,58,59,64]},{\"tag\":\"mate\",\"ridge\":13,\"a\":35,\"owners\":[13,14,15,16,59,64]},{\"tag\":\"mate\",\"ridge\":13,\"a\":62,\"owners\":[0,13,14,16,36,59,64]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[26,80,81]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[27,76,81]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[9,10,11]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[9,11,54]},{\"tag\":\"mate\",\"ridge\":21,\"a\":67,\"owners\":[1,13,17,39,59,60,66,68]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[1,67,68]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[13,18,68]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[17,18,68]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[17,67,68]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[18,57,68]},{\"tag\":\"mate\",\"ridge\":35,\"a\":2,\"owners\":[6,9,46,47,48,52,53,56]},{\"tag\":\"mate\",\"ridge\":35,\"a\":40,\"owners\":[6,9,47,48,52,53,56]},{\"tag\":\"mate\",\"ridge\":35,\"a\":41,\"owners\":[6,9,46,47,48,53,56]},{\"tag\":\"mate\",\"ridge\":35,\"a\":42,\"owners\":[6,9,46,47,52,53]},{\"tag\":\"mate\",\"ridge\":35,\"a\":48,\"owners\":[2,9,40,41,52,53]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[6,40,56]},{\"tag\":\"mate\",\"ridge\":37,\"a\":19,\"owners\":[2,14,17,40,41,61,65]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[2,17,61]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[2,19,65]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[14,19,41]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[17,19,41]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[19,40,65]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[19,41,61]},{\"tag\":\"mate\",\"ridge\":38,\"a\":79,\"owners\":[2,28,40,41,82]},{\"tag\":\"mate\",\"ridge\":38,\"a\":82,\"owners\":[2,26,40,42,78,79]},{\"tag\":\"mate\",\"ridge\":67,\"a\":7,\"owners\":[3,12,38,40,54]},{\"tag\":\"mate\",\"ridge\":67,\"a\":50,\"owners\":[3,12,38,40,54]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[3,63,67]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[40,63,67]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[27,40,83]},{\"tag\":\"mate\",\"ridge\":131,\"a\":49,\"owners\":[4,10,41,52,55]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[12,41,55]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[41,49,55]},{\"tag\":\"mate\",\"ridge\":25,\"a\":13,\"owners\":[5,21,22,44,45,70,71,72]},{\"tag\":\"mate\",\"ridge\":25,\"a\":57,\"owners\":[5,21,22,45,70,72]},{\"tag\":\"mate\",\"ridge\":41,\"a\":73,\"owners\":[6,14,21,46,61]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[6,14,73]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[6,21,73]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[6,61,73]},{\"tag\":\"mate\",\"ridge\":73,\"a\":15,\"owners\":[7,44,46,49,50,71]},{\"tag\":\"mate\",\"ridge\":73,\"a\":63,\"owners\":[7,44,46,49,50,71]},{\"tag\":\"mate\",\"ridge\":74,\"a\":7,\"owners\":[27,75,78,80,85]},{\"tag\":\"mate\",\"ridge\":74,\"a\":27,\"owners\":[7,44,46,49,50,85]},{\"tag\":\"mate\",\"ridge\":74,\"a\":44,\"owners\":[27,78,80]},{\"tag\":\"mate\",\"ridge\":74,\"a\":46,\"owners\":[27,75,80,85]},{\"tag\":\"mate\",\"ridge\":74,\"a\":50,\"owners\":[27,75,78,80,85]},{\"tag\":\"mate\",\"ridge\":74,\"a\":75,\"owners\":[7,46,49,50]},{\"tag\":\"mate\",\"ridge\":74,\"a\":78,\"owners\":[7,44,49,50,85]},{\"tag\":\"mate\",\"ridge\":74,\"a\":80,\"owners\":[7,44,46,50]},{\"tag\":\"mate\",\"ridge\":259,\"a\":50,\"owners\":[11,39,43,53,55,56]},{\"tag\":\"mate\",\"ridge\":259,\"a\":55,\"owners\":[8,36,43,47,50,51,56]},{\"tag\":\"mate\",\"ridge\":266,\"a\":8,\"owners\":[32,77,81,84,86]},{\"tag\":\"mate\",\"ridge\":266,\"a\":32,\"owners\":[8,36,47,50,51,81,86]},{\"tag\":\"mate\",\"ridge\":266,\"a\":50,\"owners\":[32,77,81,84,86]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[8,77,86]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[50,77,86]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[50,81,84]},{\"tag\":\"mate\",\"ridge\":49,\"a\":21,\"owners\":[9,17,52,53,65,66,74]},{\"tag\":\"three\",\"ridge\":50,\"vertices\":[9,82,84]},{\"tag\":\"mate\",\"ridge\":145,\"a\":10,\"owners\":[18,58,65,67,71]},{\"tag\":\"mate\",\"ridge\":145,\"a\":18,\"owners\":[10,45,52,54,55,71]},{\"tag\":\"mate\",\"ridge\":145,\"a\":55,\"owners\":[18,58,65,67,71]},{\"tag\":\"mate\",\"ridge\":145,\"a\":67,\"owners\":[10,45,52,55]},{\"tag\":\"mate\",\"ridge\":146,\"a\":29,\"owners\":[10,45,52,54,55,85]},{\"tag\":\"mate\",\"ridge\":146,\"a\":76,\"owners\":[10,52,54,55]},{\"tag\":\"mate\",\"ridge\":146,\"a\":82,\"owners\":[10,45,54,55,85]},{\"tag\":\"mate\",\"ridge\":146,\"a\":83,\"owners\":[10,45,52,55]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[11,59,74]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[11,68,69]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[22,55,68]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[55,59,74]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[55,68,69]},{\"tag\":\"mate\",\"ridge\":274,\"a\":11,\"owners\":[32,77,84]},{\"tag\":\"mate\",\"ridge\":274,\"a\":32,\"owners\":[11,39,53,55]},{\"tag\":\"mate\",\"ridge\":193,\"a\":20,\"owners\":[12,49,54,71]},{\"tag\":\"mate\",\"ridge\":193,\"a\":62,\"owners\":[12,54]},{\"tag\":\"mate\",\"ridge\":194,\"a\":30,\"owners\":[12,49,54,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":80,\"owners\":[12,54]},{\"tag\":\"mate\",\"ridge\":28,\"a\":89,\"owners\":[13,25,33,57,58,75,76,88]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[33,34,61]},{\"tag\":\"mate\",\"ridge\":76,\"a\":15,\"owners\":[27,75,78,80,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":57,\"owners\":[27,78,80]},{\"tag\":\"mate\",\"ridge\":76,\"a\":61,\"owners\":[27,75,80,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":63,\"owners\":[27,75,78,80,88]},{\"tag\":\"mate\",\"ridge\":517,\"a\":19,\"owners\":[16,37,43,60,63,64,68]},{\"tag\":\"mate\",\"ridge\":517,\"a\":42,\"owners\":[16,60,63,64,68]},{\"tag\":\"mate\",\"ridge\":517,\"a\":63,\"owners\":[19,42,43,66,68]},{\"tag\":\"mate\",\"ridge\":517,\"a\":64,\"owners\":[19,42,66]},{\"tag\":\"mate\",\"ridge\":517,\"a\":68,\"owners\":[16,19,37,42,63]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[19,43,63]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[19,63,68]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[42,63,68]},{\"tag\":\"mate\",\"ridge\":524,\"a\":34,\"owners\":[16,37,60,63,64,81,89]},{\"tag\":\"mate\",\"ridge\":524,\"a\":79,\"owners\":[16,60,63,64,89]},{\"tag\":\"mate\",\"ridge\":524,\"a\":87,\"owners\":[16,37,63,64,81]},{\"tag\":\"mate\",\"ridge\":524,\"a\":89,\"owners\":[16,34,37,63,79]},{\"tag\":\"three\",\"ridge\":524,\"vertices\":[34,63,81]},{\"tag\":\"three\",\"ridge\":524,\"vertices\":[34,63,89]},{\"tag\":\"three\",\"ridge\":524,\"vertices\":[63,81,87]},{\"tag\":\"mate\",\"ridge\":52,\"a\":82,\"owners\":[17,33,66,87]},{\"tag\":\"mate\",\"ridge\":148,\"a\":82,\"owners\":[18,58,67,88]},{\"tag\":\"mate\",\"ridge\":545,\"a\":23,\"owners\":[19,42,56,66,74]},{\"tag\":\"mate\",\"ridge\":545,\"a\":42,\"owners\":[23,70,73,74]},{\"tag\":\"mate\",\"ridge\":545,\"a\":73,\"owners\":[19,42,66]},{\"tag\":\"mate\",\"ridge\":548,\"a\":42,\"owners\":[34,87]},{\"tag\":\"three\",\"ridge\":280,\"vertices\":[32,59,90]},{\"tag\":\"three\",\"ridge\":280,\"vertices\":[32,69,89]},{\"tag\":\"mate\",\"ridge\":552,\"a\":23,\"owners\":[34,79,86,87,90]},{\"tag\":\"mate\",\"ridge\":552,\"a\":70,\"owners\":[34,79,86]},{\"tag\":\"mate\",\"ridge\":552,\"a\":79,\"owners\":[23,70,73,90]},{\"tag\":\"mate\",\"ridge\":769,\"a\":51,\"owners\":[68,74]},{\"tag\":\"mate\",\"ridge\":769,\"a\":64,\"owners\":[56,74]},{\"tag\":\"mate\",\"ridge\":769,\"a\":73,\"owners\":[43,68]},{\"tag\":\"mate\",\"ridge\":776,\"a\":24,\"owners\":[81,86,89,90]},{\"tag\":\"mate\",\"ridge\":776,\"a\":51,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":776,\"a\":64,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":776,\"a\":72,\"owners\":[81,86]},{\"tag\":\"mate\",\"ridge\":776,\"a\":73,\"owners\":[81,89]},{\"tag\":\"mate\",\"ridge\":774,\"a\":43,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":774,\"a\":81,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":802,\"a\":56,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":802,\"a\":86,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":788,\"a\":68,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":788,\"a\":89,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":816,\"a\":74,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":816,\"a\":90,\"owners\":[74]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,91]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-5,92]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-6,93]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-7,94]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-8,95]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-9,96]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-10,97]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-11,98]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-12,99]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-14,100]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-15,101]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-16,102]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-19,103]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-20,104]},{\"tag\":\"group_take\",\"kind\":1,\"index\":32,\"member\":32,\"full_literals\":[-32,105]},{\"tag\":\"group_take\",\"kind\":1,\"index\":34,\"member\":34,\"full_literals\":[-34,106]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-107,false,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-93,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-95,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-94,false,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-110,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-109,false,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-111,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-108,false,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-96,-97,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-99,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-98,-99,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0017\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-116,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-113,-115,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-113,-116,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0017\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-114,-115,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-100,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0029\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-120,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-101,false,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-121,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-119,false,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15,16],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0018\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-117,false,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15,16],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0018\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-117,-122,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15,16],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0018\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-118,false,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15,16],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-123,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15,16],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-124,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15,16],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-112,-123,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0033\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18],\"right\":[19,20],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-128,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18],\"right\":[19,20],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-127,-128,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20],\"right\":[21,22,23,24,25],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-129,false,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20],\"right\":[21,22,23,24,25],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0035\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-130,false,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[33],\"right\":[34],\"left_name\":\"grouped1_0048\",\"right_name\":\"grouped1_0050\",\"joined_name\":\"grouped1_0049\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[32],\"right\":[33,34],\"left_name\":\"grouped1_0046\",\"right_name\":\"grouped1_0049\",\"joined_name\":\"grouped1_0047\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[32],\"right\":[33,34],\"left_name\":\"grouped1_0046\",\"right_name\":\"grouped1_0049\",\"joined_name\":\"grouped1_0047\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-105,-133,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30,31],\"right\":[32,33,34],\"left_name\":\"grouped1_0044\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0045\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-134,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30,31],\"right\":[32,33,34],\"left_name\":\"grouped1_0044\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0045\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-135,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26,27,28,29],\"right\":[30,31,32,33,34],\"left_name\":\"grouped1_0042\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0043\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-136,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26,27,28,29],\"right\":[30,31,32,33,34],\"left_name\":\"grouped1_0042\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0043\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-137,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20,21,22,23,24,25],\"right\":[26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0036\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-139,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20,21,22,23,24,25],\"right\":[26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0036\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-131,-138,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20,21,22,23,24,25],\"right\":[26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0036\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-132,-138,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],\"right\":[17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-125,-141,142],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],\"right\":[17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-126,-140,142],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[38,39,44,45,52,53,54,55],\"full_literals\":[-143,38,39,44,45,52,53,54,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[60,66,70,72,87],\"full_literals\":[-144,60,66,70,72,87]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[41,82,83],\"full_literals\":[-145,41,82,83]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[75,76,77,84],\"full_literals\":[-146,75,76,77,84]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[37,42,48,51,79],\"full_literals\":[-147,37,42,48,51,79]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":37,\"full_literals\":[-37,147]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":42,\"full_literals\":[-42,147]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":48,\"full_literals\":[-48,147]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":79,\"full_literals\":[-79,147]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[35,36,46,47,49,50],\"full_literals\":[-148,35,36,46,47,49,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[57,59,61,63,64],\"full_literals\":[-149,57,59,61,63,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[58,62,67],\"full_literals\":[-150,58,62,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[40,78,80],\"full_literals\":[-151,40,78,80]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[65],\"full_literals\":[-152,65]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":65,\"full_literals\":[-65,152]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[69,73],\"full_literals\":[-153,69,73]},{\"tag\":\"group_take\",\"kind\":2,\"index\":10,\"member\":73,\"full_literals\":[-73,153]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-154,143,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-155,false,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0059\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-156,146,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0059\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-157,146,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0059\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-157,false,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0057\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-158,145,156],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0057\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-159,145,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0057\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-160,145,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0057\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-159,false,156],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0057\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-160,false,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-161,154,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-161,155,159],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-162,155,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-163,155,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-161,false,158],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-162,false,159],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-163,false,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0064\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0065\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-164,149,150],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0064\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0065\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-165,149,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0064\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0065\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-165,false,150],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0065\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-167,148,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0065\",\"joined_name\":\"grouped2_0062\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-166,false,164],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0065\",\"joined_name\":\"grouped2_0062\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-167,false,165],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0069\",\"right_name\":\"grouped2_0071\",\"joined_name\":\"grouped2_0070\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-168,152,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0069\",\"right_name\":\"grouped2_0071\",\"joined_name\":\"grouped2_0070\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-169,152,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0069\",\"right_name\":\"grouped2_0071\",\"joined_name\":\"grouped2_0070\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-169,false,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0069\",\"right_name\":\"grouped2_0071\",\"joined_name\":\"grouped2_0070\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-152,-153,169],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0067\",\"right_name\":\"grouped2_0070\",\"joined_name\":\"grouped2_0068\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-170,151,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0067\",\"right_name\":\"grouped2_0070\",\"joined_name\":\"grouped2_0068\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-171,151,169],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0067\",\"right_name\":\"grouped2_0070\",\"joined_name\":\"grouped2_0068\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-172,151,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0067\",\"right_name\":\"grouped2_0070\",\"joined_name\":\"grouped2_0068\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-171,false,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0067\",\"right_name\":\"grouped2_0070\",\"joined_name\":\"grouped2_0068\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-172,false,169],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0063\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-174,166,172],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0063\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-173,167,170],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0063\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-174,167,171],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0063\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-175,167,172],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0063\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-176,167,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0063\",\"a\":3,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-174,false,170],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0063\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-175,false,171],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0063\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-176,false,172],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-177,161,176],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-177,162,175],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-177,163,174],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-177,false,173],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[71],\"full_literals\":[-178,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":71,\"full_literals\":[-71,178]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[85],\"full_literals\":[-179,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-85,179]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[88],\"full_literals\":[-180,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-88,180]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[43,56],\"full_literals\":[-181,43,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-56,181]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[68,74],\"full_literals\":[-182,68,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-68,182]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-74,182]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[81,86],\"full_literals\":[-183,81,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-81,183]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-86,183]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[89,90],\"full_literals\":[-184,89,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-89,184]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-90,184]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0075\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0076\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-185,179,180],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0075\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0076\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-180,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0075\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0076\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-179,false,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0073\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-186,178,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0073\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-185,186],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0073\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-178,false,186],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0081\",\"joined_name\":\"grouped3_0079\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-187,181,182],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0081\",\"joined_name\":\"grouped3_0079\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-182,187],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0081\",\"joined_name\":\"grouped3_0079\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-181,false,187],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0081\",\"joined_name\":\"grouped3_0079\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-188,false,182],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0082\",\"right_name\":\"grouped3_0084\",\"joined_name\":\"grouped3_0083\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-189,183,184],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0082\",\"right_name\":\"grouped3_0084\",\"joined_name\":\"grouped3_0083\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-184,189],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0082\",\"right_name\":\"grouped3_0084\",\"joined_name\":\"grouped3_0083\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-183,false,189],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0082\",\"right_name\":\"grouped3_0084\",\"joined_name\":\"grouped3_0083\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-190,false,184],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0082\",\"right_name\":\"grouped3_0084\",\"joined_name\":\"grouped3_0083\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-183,-184,190],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0079\",\"right_name\":\"grouped3_0083\",\"joined_name\":\"grouped3_0080\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-191,187,190],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0079\",\"right_name\":\"grouped3_0083\",\"joined_name\":\"grouped3_0080\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-191,188,189],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0079\",\"right_name\":\"grouped3_0083\",\"joined_name\":\"grouped3_0080\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-187,-189,191],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0079\",\"right_name\":\"grouped3_0083\",\"joined_name\":\"grouped3_0080\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-187,-190,192],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-193,186,191],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-192,194],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-186,-191,194],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":15,\"owners\":[8,11,32,36,39,43,47,50,51,53,55,56,77,81,84,86]},{\"tag\":\"edge\",\"edge\":20,\"owners\":[3,15,20,27,30,38,40,57,61,62,63,67,75,78,80,83,88]},{\"tag\":\"edge\",\"edge\":23,\"owners\":[16,19,34,37,42,43,60,63,64,66,68,79,81,87,89]},{\"tag\":\"edge\",\"edge\":26,\"owners\":[7,15,27,44,46,49,50,57,61,62,63,71,75,78,80,85,88]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[10,18,29,45,52,54,55,58,65,67,71,76,82,83,85,88]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[19,23,34,42,48,56,66,70,73,74,79,86,87,90]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[24,43,51,56,64,68,72,73,74,81,86,89,90]}]}"
  "501 173 0 452 451 0\n502 -192 0 493 490 0\n503 -190 0 502 483 488 477 462 463 323 325 467 0\n504 -169 -182 43 0 432 433 404 74 461 312 107 406 0\n505 -74 -153 0 107 109 406 0\n506 -69 -89 -68 183 0 120 69 68 466 320 465 318 76 78 79 165 306 268 271 251 253 494 0\n507 32 50 55 84 53 51 47 77 39 36 183 0 466 320 465 318 251 272 494 0\n508 126 41 -99 52 45 -9 55 48 37 17 59 64 0 331 352 354 357 366 370 371 368 367 350 351 358 364 365 348 349 343 355 362 363 360 346 347 344 345 342 333 361 336 335 330 329 328 327 326 230 337 198 192 0\n509 140 -105 63 37 17 -68 0 379 381 383 180 385 386 384 376 382 374 380 373 378 339 341 288 304 0\n510 50 55 -73 -68 74 65 183 0 390 166 98 96 95 94 93 92 91 120 75 71 69 68 466 320 311 465 507 252 273 340 12 331 11 19 334 352 354 357 366 509 389 370 371 508 368 350 6 359 348 303 353 347 219 220 222 332 329 257 235 0\n511 -41 -12 46 45 7 55 53 48 47 58 65 56 186 0 19 474 472 456 471 458 475 454 20 64 149 155 212 202 260 263 264 498 0\n512 -10 -12 45 55 58 65 186 0 19 474 472 456 471 458 475 454 202 203 262 265 266 260 263 264 498 0\n513 82 83 42 3 40 41 84 51 48 37 -159 77 0 393 414 411 412 395 128 223 394 111 0\n514 11 67 42 3 40 41 52 45 55 84 51 48 37 -159 -89 -68 185 0 416 120 70 472 456 471 458 266 513 147 152 153 265 300 394 30 206 410 278 395 126 0\n515 67 -128 42 3 40 41 -138 -99 52 45 55 84 51 48 37 -159 -89 -68 65 186 0 390 70 475 454 474 514 259 333 338 355 372 356 375 366 377 369 387 388 0\n516 55 -73 -89 -68 74 65 -161 183 186 0 166 96 95 94 93 92 180 465 466 316 75 72 84 392 409 419 120 70 69 320 318 510 15 16 17 18 249 253 19 334 340 379 381 383 511 512 211 210 213 303 339 373 515 63 65 110 157 391 513 408 153 418 394 417 411 0\n517 -67 42 3 40 41 84 51 48 37 -159 -68 0 416 180 120 75 110 157 208 513 153 299 394 126 410 395 0\n518 -82 18 42 84 51 48 37 -156 87 77 66 0 152 153 299 394 126 410 395 0\n519 7 46 41 -55 -73 -159 -68 65 56 71 0 26 22 166 96 95 94 93 92 416 180 120 75 70 211 210 213 303 517 261 207 518 513 159 160 394 410 395 125 127 216 0\n520 46 41 -55 -73 -159 -68 64 65 183 186 0 269 25 24 21 98 95 93 91 84 71 70 68 465 466 316 320 318 474 472 456 471 458 475 454 519 15 236 237 238 250 234 233 193 194 195 196 197 199 242 246 248 247 497 0\n521 -46 -55 51 47 36 183 0 466 320 465 318 12 18 250 0\n522 -153 -182 -184 186 0 503 452 484 465 318 504 439 447 448 466 316 320 474 472 456 471 458 475 454 434 405 505 325 311 461 467 68 70 72 75 84 180 392 409 419 506 406 93 94 95 96 98 516 22 23 24 27 521 520 3 5 64 155 231 232 212 261 225 226 275 277 274 276 238 209 239 242 246 247 495 0\n523 -62 -149 64 59 0 43 44 49 401 0\n524 -63 10 53 79 52 -67 -68 73 43 86 0 205 64 62 322 189 180 106 84 75 69 68 320 45 46 227 228 290 291 297 190 214 301 499 0\n525 -68 153 72 43 86 0 452 407 70 71 72 73 74 75 84 120 180 322 404 392 431 409 438 421 446 450 449 442 420 430 415 417 426 427 411 523 402 64 66 110 157 208 393 150 153 299 394 126 163 258 524 401 36 37 279 295 0\n526 -61 64 87 66 60 68 81 0 323 318 36 37 39 48 127 284 292 496 0\n527 -59 -90 -74 183 0 167 103 102 466 320 465 318 31 32 34 118 267 270 305 249 507 0\n528 149 155 84 153 169 0 452 439 421 450 440 429 425 426 430 443 442 449 438 436 420 431 415 417 404 411 55 57 67 151 402 393 42 113 133 159 403 394 124 0\n529 63 64 -149 59 87 66 60 68 81 0 526 323 318 401 28 29 284 292 293 285 496 0\n530 -175 58 62 153 172 0 443 446 430 438 427 431 402 404 67 0\n531 -67 -160 84 0 417 411 415 64 110 157 393 153 154 394 0\n532 64 59 155 87 84 66 60 68 153 169 81 0 452 528 421 450 439 318 523 529 47 530 449 420 415 417 411 531 402 427 430 442 438 436 431 404 55 56 151 286 393 221 159 160 161 394 403 124 0\n533 -83 -146 77 84 0 159 160 394 0\n534 -82 -146 77 84 0 152 153 394 0\n535 -160 77 51 48 37 -170 84 153 0 415 417 411 412 533 534 393 5 6 55 395 404 128 129 431 394 435 135 403 0\n536 -184 -191 0 493 503 452 485 491 484 465 466 318 320 316 459 476 504 439 447 448 522 525 323 461 467 104 105 108 167 181 392 409 419 421 416 450 445 527 532 51 52 53 119 535 420 449 446 438 436 431 404 55 56 57 151 287 530 218 221 133 513 403 533 129 410 395 0\n537 -64 146 80 184 0 452 468 469 314 324 50 51 52 54 83 89 99 311 302 309 80 395 406 410 433 416 439 423 447 449 448 446 419 438 436 409 431 404 57 61 530 392 42 182 403 0\n538 153 -175 64 0 446 438 433 431 439 404 443 57 58 430 530 426 523 0\n539 81 -153 -183 89 0 464 317 176 406 0\n540 -175 64 80 67 -183 89 0 446 538 539 140 144 319 9 403 436 437 432 443 404 430 57 426 427 523 402 0\n541 -81 -147 51 0 136 137 138 145 395 0\n542 -147 -183 51 0 541 464 173 174 175 177 395 0\n543 146 153 82 41 147 184 0 452 433 439 447 448 422 410 416 413 423 393 449 161 538 537 0\n544 153 82 41 77 84 147 184 0 452 412 433 439 447 448 543 533 393 414 423 419 449 409 446 538 438 436 54 83 89 431 404 57 61 530 392 42 133 182 403 0\n545 -76 -81 186 0 144 142 474 472 456 471 458 475 454 112 113 135 201 243 244 245 280 281 282 283 241 497 0\n546 80 -175 40 78 64 -183 89 0 446 403 540 436 67 432 404 0\n547 82 41 77 84 -183 -191 0 493 452 536 468 469 314 542 491 544 539 141 142 144 319 9 545 394 410 416 423 449 546 132 133 161 393 413 422 448 444 447 430 439 427 432 402 404 67 0\n548 -61 -3 -67 59 39 2 68 0 59 35 41 217 204 0\n549 -82 77 84 -183 184 0 452 468 469 314 542 399 398 397 324 322 146 148 151 534 404 410 432 416 439 423 449 446 443 438 430 431 426 427 539 139 140 141 144 178 319 523 9 546 132 200 402 224 66 59 548 401 98 296 298 289 307 308 499 0\n550 -80 -150 67 0 132 133 402 0\n551 77 84 -183 -191 0 452 536 468 469 314 542 412 417 424 450 445 549 547 5 10 55 64 319 404 539 431 438 435 446 442 449 430 423 427 416 410 550 403 122 123 394 0\n552 -150 67 40 153 78 64 59 -174 0 433 445 550 403 435 436 431 442 404 430 57 426 402 523 0\n553 -171 40 -145 153 82 78 0 433 438 436 431 403 404 161 55 393 0\n554 -67 -145 82 0 64 157 393 0\n555 40 -145 153 82 78 64 59 -174 0 554 553 552 442 427 430 0\n556 -77 -183 -191 0 493 503 452 536 468 469 314 542 412 417 424 450 398 396 485 322 324 461 476 491 474 472 456 471 458 475 454 114 115 116 117 118 119 121 124 143 154 459 464 539 254 255 538 449 423 414 555 1 2 5 13 14 38 42 130 215 393 191 156 229 239 240 497 0\n557 -183 -191 0 503 452 485 536 468 322 469 324 461 476 314 542 397 398 399 412 417 424 450 445 556 551 162 164 165 166 179 459 311 406 464 7 8 9 33 538 144 256 449 423 414 555 151 404 431 438 435 442 403 428 430 131 200 426 427 400 224 552 40 82 59 66 401 296 298 289 307 499 0\n558 -191 0 536 468 469 322 324 461 557 479 480 486 0\n559 186 0 558 492 489 0\n560 -80 0 559 134 171 187 453 455 457 473 470 0\n561 -62 0 559 87 169 185 453 455 457 473 470 0\n562 -174 153 151 0 561 433 436 445 442 435 430 431 427 404 57 67 402 0\n563 -58 0 559 86 168 184 453 455 457 473 470 0\n564 -83 0 559 158 172 188 453 455 457 473 470 0\n565 -65 -145 0 564 55 151 393 0\n566 -67 0 559 88 170 186 453 455 457 473 470 0\n567 -150 0 566 563 561 402 0\n568 -165 0 567 427 0\n569 -167 0 568 430 0\n570 170 0 569 501 441 0\n571 -84 -153 0 165 166 406 0\n572 -82 84 -146 0 154 534 0\n573 -69 66 42 37 -147 -144 0 77 78 81 85 90 395 392 183 0\n574 152 151 0 570 569 452 564 435 432 431 436 442 450 421 424 409 415 417 411 412 571 572 393 4 6 10 60 319 573 406 91 97 98 99 100 101 294 392 0\n575 86 90 43 56 51 68 72 73 74 64 81 89 0 500 313 0\n576 151 0 569 452 437 443 449 423 574 404 74 565 323 414 415 412 424 450 562 505 325 310 541 542 318 317 466 320 315 316 575 0\n577 89 90 86 51 64 72 73 43 0 324 320 319 322 575 0\n578 -89 86 72 73 43 0 319 464 323 525 506 406 0\n579 -90 0 558 325 469 463 481 477 487 0\n580 86 51 64 72 73 43 0 579 578 577 0\n581 -86 0 558 321 466 460 482 478 487 0\n582 -64 0 581 579 315 0\n583 72 73 43 0 579 581 582 578 580 314 0\n584 43 0 581 558 319 316 583 312 317 462 468 477 481 487 0\n585 -40 0 584 9 0\n586 81 0 584 318 0\n587 78 0 585 560 576 403 0\n588 0 586 587 144 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record001
