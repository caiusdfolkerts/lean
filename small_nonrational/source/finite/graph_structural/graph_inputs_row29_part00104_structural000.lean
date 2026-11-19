module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00104Frames
public import GraphInputsRow29Part00104Leaves
public import GraphInputsRow29Part00104Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3e0f43b0dc2f07c2e87a2d8b92d4752ccab26c3b29c970dcac9b25caaa6a96aa6aa6a599655a8e8b8ae1ba1e2785e6c6715c5a99a56996665656555564d8b4ad1b61d2745d68d6364d534ccb31cd8b52d2b2ac6b26c5b61d4729c6745c9715c8f13c2f07ea89a2949528c931a2648aa2588e585511a4551352344c2b05c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69b69a49a4da6936d269a6d36d349b6926d36924936da49b6db492491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.data.quota

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
 (.branch 18
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)]))))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.leaf ([(facetIndex 20)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "149ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 21
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 61), (facetIndex 80)]))
 (.leaf ([(facetIndex 88), (facetIndex 90), (facetIndex 94)])))
 (.branch 3
 (.leaf ([(facetIndex 52), (facetIndex 54), (facetIndex 59)]))
 (.branch 4
 (.leaf ([(facetIndex 27), (facetIndex 53), (facetIndex 72)]))
 (.leaf ([(facetIndex 36), (facetIndex 58), (facetIndex 77)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 70), (facetIndex 73), (facetIndex 78)]))
 (.leaf ([(facetIndex 21), (facetIndex 46), (facetIndex 65), (facetIndex 83), (facetIndex 84)])))
 (.branch 8
 (.leaf ([(facetIndex 24), (facetIndex 26), (facetIndex 35), (facetIndex 43), (facetIndex 45)]))
 (.branch 9
 (.leaf ([(facetIndex 23), (facetIndex 25), (facetIndex 34), (facetIndex 42), (facetIndex 44)]))
 (.leaf ([(facetIndex 22), (facetIndex 49), (facetIndex 68), (facetIndex 86), (facetIndex 87)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10001019906600005400053050900600000240002320090067878000004780000003787896z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 95), (facetIndex 97), (facetIndex 99)]))
 (.leaf ([(facetIndex 96), (facetIndex 98), (facetIndex 100)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 32), (facetIndex 37), (facetIndex 39)]))
 (.branch 4
 (.leaf ([(facetIndex 29), (facetIndex 31), (facetIndex 33), (facetIndex 38), (facetIndex 40)]))
 (.leaf ([(facetIndex 48), (facetIndex 51), (facetIndex 62)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 47), (facetIndex 57), (facetIndex 64), (facetIndex 66), (facetIndex 82)]))
 (.branch 7
 (.leaf ([(facetIndex 50), (facetIndex 55), (facetIndex 60), (facetIndex 63)]))
 (.leaf ([(facetIndex 69), (facetIndex 75), (facetIndex 81)]))))
 (.branch 9
 (.leaf ([(facetIndex 67), (facetIndex 71), (facetIndex 76), (facetIndex 79)]))
 (.branch 10
 (.leaf ([(facetIndex 56), (facetIndex 74), (facetIndex 85)]))
 (.leaf ([(facetIndex 89), (facetIndex 91), (facetIndex 92), (facetIndex 93)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1010100aaa0a0009005708008790080708505640600596000460450000003232000323232z1c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
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
def grouped1_0023 : List Nat := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
def grouped1_0024 : List Nat := [11]
def grouped1_0025 : List Nat := [12]
def grouped1_0026 : List Nat := [12, 13, 14]
def grouped1_0027 : List Nat := [13]
def grouped1_0028 : List Nat := [13, 14]
def grouped1_0029 : List Nat := [14]
def grouped1_0030 : List Nat := [15]
def grouped1_0031 : List Nat := [15, 16, 17]
def grouped1_0032 : List Nat := [15, 16, 17, 18, 19, 20]
def grouped1_0033 : List Nat := [16]
def grouped1_0034 : List Nat := [16, 17]
def grouped1_0035 : List Nat := [17]
def grouped1_0036 : List Nat := [18]
def grouped1_0037 : List Nat := [18, 19, 20]
def grouped1_0038 : List Nat := [19]
def grouped1_0039 : List Nat := [19, 20]
def grouped1_0040 : List Nat := [20]
def grouped2_0041 : List Nat := [0]
def grouped2_0042 : List Nat := [0, 1]
def grouped2_0043 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0045 : List Nat := [1]
def grouped2_0046 : List Nat := [2]
def grouped2_0047 : List Nat := [2, 3, 4]
def grouped2_0048 : List Nat := [3]
def grouped2_0049 : List Nat := [3, 4]
def grouped2_0050 : List Nat := [4]
def grouped2_0051 : List Nat := [5]
def grouped2_0052 : List Nat := [5, 6]
def grouped2_0053 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0054 : List Nat := [6]
def grouped2_0055 : List Nat := [7]
def grouped2_0056 : List Nat := [7, 8, 9]
def grouped2_0057 : List Nat := [8]
def grouped2_0058 : List Nat := [8, 9]
def grouped2_0059 : List Nat := [9]
def grouped3_0060 : List Nat := [0]
def grouped3_0061 : List Nat := [0, 1]
def grouped3_0062 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0064 : List Nat := [1]
def grouped3_0065 : List Nat := [2]
def grouped3_0066 : List Nat := [2, 3, 4]
def grouped3_0067 : List Nat := [3]
def grouped3_0068 : List Nat := [3, 4]
def grouped3_0069 : List Nat := [4]
def grouped3_0070 : List Nat := [5]
def grouped3_0071 : List Nat := [5, 6, 7]
def grouped3_0072 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0073 : List Nat := [6]
def grouped3_0074 : List Nat := [6, 7]
def grouped3_0075 : List Nat := [7]
def grouped3_0076 : List Nat := [8]
def grouped3_0077 : List Nat := [8, 9, 10]
def grouped3_0078 : List Nat := [9]
def grouped3_0079 : List Nat := [9, 10]
def grouped3_0080 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_matrix_checked

def leafCount : Nat := 398
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 12), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 20), (facetIndex 24), (facetIndex 34), (facetIndex 41), (facetIndex 54), (facetIndex 72), (facetIndex 77), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 17), (facetIndex 18), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 65), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 16), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 65), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 14), (facetIndex 24), (facetIndex 34), (facetIndex 41), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 12), (facetIndex 19), (facetIndex 20), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 16), (facetIndex 19), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 65), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 13), (facetIndex 19), (facetIndex 20), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 14), (facetIndex 15), (facetIndex 18), (facetIndex 21), (facetIndex 35), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 15), (facetIndex 19), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 95), (facetIndex 96)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 7), (facetIndex 9), (facetIndex 14), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 95), (facetIndex 96)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 4), (facetIndex 5), (facetIndex 20), (facetIndex 24), (facetIndex 34), (facetIndex 54), (facetIndex 61), (facetIndex 72), (facetIndex 77), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 1), (facetIndex 4), (facetIndex 9), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 14), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 65), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 8), (facetIndex 15), (facetIndex 24), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 72), (facetIndex 77), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 8), (facetIndex 15), (facetIndex 24), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 72), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 46), (facetIndex 72), (facetIndex 78), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 15), (facetIndex 16), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 65), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 7), (facetIndex 9), (facetIndex 14), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 97), (facetIndex 98)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 15), (facetIndex 19), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 97), (facetIndex 98)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 17), (facetIndex 20), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 68), (facetIndex 73), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 15), (facetIndex 19), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 7), (facetIndex 9), (facetIndex 14), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 9), (facetIndex 13), (facetIndex 19), (facetIndex 24), (facetIndex 34), (facetIndex 41), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leaf0027 : List (Fin data.count) := [(facetIndex 1), (facetIndex 8), (facetIndex 14), (facetIndex 18), (facetIndex 20), (facetIndex 23), (facetIndex 35), (facetIndex 41), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0027_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0027 = true := by
  decide +kernel
theorem leaf0027_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0027 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0027_counts_checked
def leaf0028 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 8), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0028_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0028 = true := by
  decide +kernel
theorem leaf0028_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0028 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0028_counts_checked
def leaf0029 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 13), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0029_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0029 = true := by
  decide +kernel
theorem leaf0029_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0029 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0029_counts_checked
def leaf0030 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 13), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0030_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0030 = true := by
  decide +kernel
theorem leaf0030_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0030 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0030_counts_checked
def leaf0031 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 14), (facetIndex 17), (facetIndex 19), (facetIndex 24), (facetIndex 25), (facetIndex 36), (facetIndex 52), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0031_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0031 = true := by
  decide +kernel
theorem leaf0031_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0031 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0031_counts_checked
def leaf0032 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 14), (facetIndex 16), (facetIndex 18), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 54), (facetIndex 61), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0032_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0032 = true := by
  decide +kernel
theorem leaf0032_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0032 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0032_counts_checked
def leaf0033 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 6), (facetIndex 9), (facetIndex 12), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0033_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0033 = true := by
  decide +kernel
theorem leaf0033_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0033 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0033_counts_checked
def leaf0034 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 14), (facetIndex 16), (facetIndex 20), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 59), (facetIndex 61), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0034_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0034 = true := by
  decide +kernel
theorem leaf0034_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0034 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0034_counts_checked
def leaf0035 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 7), (facetIndex 9), (facetIndex 11), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0035_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0035 = true := by
  decide +kernel
theorem leaf0035_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0035 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0035_counts_checked
def leaf0036 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 4), (facetIndex 9), (facetIndex 19), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 65), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0036_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0036 = true := by
  decide +kernel
theorem leaf0036_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0036 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0036_counts_checked
def leaf0037 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 6), (facetIndex 17), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 68), (facetIndex 72), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0037_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0037 = true := by
  decide +kernel
theorem leaf0037_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0037 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0037_counts_checked
def leaf0038 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 5), (facetIndex 13), (facetIndex 24), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 95), (facetIndex 96)]
theorem leaf0038_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0038 = true := by
  decide +kernel
theorem leaf0038_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0038 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0038_counts_checked
def leaf0039 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 5), (facetIndex 13), (facetIndex 24), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 97), (facetIndex 98)]
theorem leaf0039_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0039 = true := by
  decide +kernel
theorem leaf0039_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0039 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0039_counts_checked
def leaf0040 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 8), (facetIndex 15), (facetIndex 23), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 68), (facetIndex 72), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0040_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0040 = true := by
  decide +kernel
theorem leaf0040_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0040 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0040_counts_checked
def leaf0041 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 9), (facetIndex 16), (facetIndex 20), (facetIndex 23), (facetIndex 36), (facetIndex 53), (facetIndex 59), (facetIndex 68), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0041_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0041 = true := by
  decide +kernel
theorem leaf0041_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0041 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0041_counts_checked
def leaf0042 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 5), (facetIndex 9), (facetIndex 12), (facetIndex 24), (facetIndex 36), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0042_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0042 = true := by
  decide +kernel
theorem leaf0042_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0042 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0042_counts_checked
def leaf0043 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 8), (facetIndex 14), (facetIndex 24), (facetIndex 41), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0043_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0043 = true := by
  decide +kernel
theorem leaf0043_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0043 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0043_counts_checked
def leaf0044 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 5), (facetIndex 13), (facetIndex 24), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0044_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0044 = true := by
  decide +kernel
theorem leaf0044_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0044 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0044_counts_checked
def leaf0045 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 4), (facetIndex 5), (facetIndex 14), (facetIndex 24), (facetIndex 34), (facetIndex 54), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0045_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0045 = true := by
  decide +kernel
theorem leaf0045_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0045 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0045_counts_checked
def leaf0046 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 5), (facetIndex 7), (facetIndex 14), (facetIndex 24), (facetIndex 36), (facetIndex 54), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0046_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0046 = true := by
  decide +kernel
theorem leaf0046_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0046 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0046_counts_checked
def leaf0047 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 95), (facetIndex 96)]
theorem leaf0047_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0047 = true := by
  decide +kernel
theorem leaf0047_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0047 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0047_counts_checked
def leaf0048 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 97), (facetIndex 98)]
theorem leaf0048_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0048 = true := by
  decide +kernel
theorem leaf0048_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0048 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0048_counts_checked
def leaf0049 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 15), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 68), (facetIndex 72), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0049_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0049 = true := by
  decide +kernel
theorem leaf0049_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0049 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0049_counts_checked
def leaf0050 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 5), (facetIndex 12), (facetIndex 24), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0050_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0050 = true := by
  decide +kernel
theorem leaf0050_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0050 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0050_counts_checked
def leaf0051 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 14), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 52), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0051_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0051 = true := by
  decide +kernel
theorem leaf0051_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0051 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0051_counts_checked
def leaf0052 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 12), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0052_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0052 = true := by
  decide +kernel
theorem leaf0052_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0052 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0052_counts_checked
def leaf0053 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 11), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0053_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0053 = true := by
  decide +kernel
theorem leaf0053_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0053 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0053_counts_checked
def leaf0054 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 11), (facetIndex 15), (facetIndex 19), (facetIndex 24), (facetIndex 27), (facetIndex 36), (facetIndex 49), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0054_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0054 = true := by
  decide +kernel
theorem leaf0054_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0054 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0054_counts_checked
def leaf0055 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 12), (facetIndex 15), (facetIndex 17), (facetIndex 24), (facetIndex 27), (facetIndex 36), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0055_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0055 = true := by
  decide +kernel
theorem leaf0055_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0055 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0055_counts_checked
def leaf0056 : List (Fin data.count) := [(facetIndex 6), (facetIndex 13), (facetIndex 14), (facetIndex 16), (facetIndex 20), (facetIndex 23), (facetIndex 27), (facetIndex 36), (facetIndex 59), (facetIndex 61), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0056_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0056 = true := by
  decide +kernel
theorem leaf0056_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0056 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0056_counts_checked
def leaf0057 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 14), (facetIndex 16), (facetIndex 18), (facetIndex 23), (facetIndex 27), (facetIndex 36), (facetIndex 54), (facetIndex 61), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0057_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0057 = true := by
  decide +kernel
theorem leaf0057_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0057 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0057_counts_checked
def leaf0058 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0058_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0058 = true := by
  decide +kernel
theorem leaf0058_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0058 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0058_counts_checked
def leaf0059 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0059_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0059 = true := by
  decide +kernel
theorem leaf0059_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0059 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0059_counts_checked
def leaf0060 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 12), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0060_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0060 = true := by
  decide +kernel
theorem leaf0060_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0060 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0060_counts_checked
def leaf0061 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 8), (facetIndex 9), (facetIndex 12), (facetIndex 24), (facetIndex 27), (facetIndex 36), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0061_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0061 = true := by
  decide +kernel
theorem leaf0061_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0061 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0061_counts_checked
def leaf0062 : List (Fin data.count) := [(facetIndex 5), (facetIndex 7), (facetIndex 8), (facetIndex 9), (facetIndex 11), (facetIndex 24), (facetIndex 27), (facetIndex 36), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0062_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0062 = true := by
  decide +kernel
theorem leaf0062_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0062 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0062_counts_checked
def leaf0063 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 14), (facetIndex 23), (facetIndex 27), (facetIndex 36), (facetIndex 54), (facetIndex 61), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0063_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0063 = true := by
  decide +kernel
theorem leaf0063_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0063 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0063_counts_checked
def leaf0064 : List (Fin data.count) := [(facetIndex 6), (facetIndex 10), (facetIndex 12), (facetIndex 13), (facetIndex 14), (facetIndex 23), (facetIndex 27), (facetIndex 36), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0064_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0064 = true := by
  decide +kernel
theorem leaf0064_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0064 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0064_counts_checked
def leaf0065 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 18), (facetIndex 24), (facetIndex 25), (facetIndex 41), (facetIndex 59), (facetIndex 72), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0065_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0065 = true := by
  decide +kernel
theorem leaf0065_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0065 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0065_counts_checked
def leaf0066 : List (Fin data.count) := [(facetIndex 1), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 19), (facetIndex 23), (facetIndex 35), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0066_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0066 = true := by
  decide +kernel
theorem leaf0066_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0066 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0066_counts_checked
def leaf0067 : List (Fin data.count) := [(facetIndex 2), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 17), (facetIndex 23), (facetIndex 26), (facetIndex 41), (facetIndex 53), (facetIndex 58), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0067_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0067 = true := by
  decide +kernel
theorem leaf0067_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0067 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0067_counts_checked
def leaf0068 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 14), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 65), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0068_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0068 = true := by
  decide +kernel
theorem leaf0068_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0068 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0068_counts_checked
def leaf0069 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 13), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0069_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0069 = true := by
  decide +kernel
theorem leaf0069_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0069 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0069_counts_checked
def leaf0070 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 10), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 46), (facetIndex 59), (facetIndex 72), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0070_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0070 = true := by
  decide +kernel
theorem leaf0070_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0070 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0070_counts_checked
def leaf0071 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 10), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 73), (facetIndex 77), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0071_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0071 = true := by
  decide +kernel
theorem leaf0071_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0071 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0071_counts_checked
def leaf0072 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 19), (facetIndex 20), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0072_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0072 = true := by
  decide +kernel
theorem leaf0072_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0072 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0072_counts_checked
def leaf0073 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 17), (facetIndex 18), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 72), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0073_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0073 = true := by
  decide +kernel
theorem leaf0073_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0073 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0073_counts_checked
def leaf0074 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 19), (facetIndex 20), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 73), (facetIndex 77), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0074_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0074 = true := by
  decide +kernel
theorem leaf0074_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0074 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0074_counts_checked
def leaf0075 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 34), (facetIndex 41), (facetIndex 54), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0075_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0075 = true := by
  decide +kernel
theorem leaf0075_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0075 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0075_counts_checked
def leaf0076 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 25), (facetIndex 41), (facetIndex 59), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0076_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0076 = true := by
  decide +kernel
theorem leaf0076_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0076 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0076_counts_checked
def leaf0077 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 35), (facetIndex 41), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 73), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0077_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0077 = true := by
  decide +kernel
theorem leaf0077_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0077 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0077_counts_checked
def leaf0078 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 26), (facetIndex 41), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0078_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0078 = true := by
  decide +kernel
theorem leaf0078_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0078 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0078_counts_checked
def leaf0079 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 16), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 68), (facetIndex 72), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0079_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0079 = true := by
  decide +kernel
theorem leaf0079_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0079 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0079_counts_checked
def leaf0080 : List (Fin data.count) := [(facetIndex 1), (facetIndex 12), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 46), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0080_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0080 = true := by
  decide +kernel
theorem leaf0080_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0080 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0080_counts_checked
def leaf0081 : List (Fin data.count) := [(facetIndex 2), (facetIndex 11), (facetIndex 15), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 49), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0081_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0081 = true := by
  decide +kernel
theorem leaf0081_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0081 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0081_counts_checked
def leaf0082 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 11), (facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0082_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0082 = true := by
  decide +kernel
theorem leaf0082_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0082 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0082_counts_checked
def leaf0083 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 12), (facetIndex 24), (facetIndex 25), (facetIndex 36), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0083_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0083 = true := by
  decide +kernel
theorem leaf0083_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0083 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0083_counts_checked
def leaf0084 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 23), (facetIndex 27), (facetIndex 35), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0084_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0084 = true := by
  decide +kernel
theorem leaf0084_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0084 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0084_counts_checked
def leaf0085 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 23), (facetIndex 26), (facetIndex 36), (facetIndex 54), (facetIndex 61), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0085_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0085 = true := by
  decide +kernel
theorem leaf0085_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0085 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0085_counts_checked
def leaf0086 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 13), (facetIndex 24), (facetIndex 25), (facetIndex 41), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0086_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0086 = true := by
  decide +kernel
theorem leaf0086_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0086 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0086_counts_checked
def leaf0087 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 23), (facetIndex 35), (facetIndex 41), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0087_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0087 = true := by
  decide +kernel
theorem leaf0087_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0087 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0087_counts_checked
def leaf0088 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 23), (facetIndex 26), (facetIndex 41), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0088_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0088 = true := by
  decide +kernel
theorem leaf0088_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0088 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0088_counts_checked
def leaf0089 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 65), (facetIndex 77), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0089_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0089 = true := by
  decide +kernel
theorem leaf0089_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0089 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0089_counts_checked
def leaf0090 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 18), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 68), (facetIndex 72), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0090_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0090 = true := by
  decide +kernel
theorem leaf0090_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0090 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0090_counts_checked
def leaf0091 : List (Fin data.count) := [(facetIndex 1), (facetIndex 10), (facetIndex 17), (facetIndex 18), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 46), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0091_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0091 = true := by
  decide +kernel
theorem leaf0091_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0091 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0091_counts_checked
def leaf0092 : List (Fin data.count) := [(facetIndex 2), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 20), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 49), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0092_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0092 = true := by
  decide +kernel
theorem leaf0092_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0092 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0092_counts_checked
def leaf0093 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0093_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0093 = true := by
  decide +kernel
theorem leaf0093_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0093 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0093_counts_checked
def leaf0094 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 11), (facetIndex 19), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0094_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0094 = true := by
  decide +kernel
theorem leaf0094_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0094 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0094_counts_checked
def leaf0095 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 12), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0095_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0095 = true := by
  decide +kernel
theorem leaf0095_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0095 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0095_counts_checked
def leaf0096 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 12), (facetIndex 13), (facetIndex 14), (facetIndex 24), (facetIndex 27), (facetIndex 36), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0096_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0096 = true := by
  decide +kernel
theorem leaf0096_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0096 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0096_counts_checked
def leaf0097 : List (Fin data.count) := [(facetIndex 5), (facetIndex 7), (facetIndex 11), (facetIndex 13), (facetIndex 14), (facetIndex 24), (facetIndex 27), (facetIndex 36), (facetIndex 54), (facetIndex 61), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0097_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0097 = true := by
  decide +kernel
theorem leaf0097_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0097 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0097_counts_checked
def leaf0098 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 11), (facetIndex 23), (facetIndex 27), (facetIndex 36), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0098_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0098 = true := by
  decide +kernel
theorem leaf0098_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0098 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0098_counts_checked
def leaf0099 : List (Fin data.count) := [(facetIndex 6), (facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 23), (facetIndex 27), (facetIndex 36), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0099_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0099 = true := by
  decide +kernel
theorem leaf0099_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0099 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0099_counts_checked
def leaf0100 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 16), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 68), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0100_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0100 = true := by
  decide +kernel
theorem leaf0100_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0100 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0100_counts_checked
def leaf0101 : List (Fin data.count) := [(facetIndex 1), (facetIndex 12), (facetIndex 15), (facetIndex 19), (facetIndex 20), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 46), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0101_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0101 = true := by
  decide +kernel
theorem leaf0101_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0101 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0101_counts_checked
def leaf0102 : List (Fin data.count) := [(facetIndex 2), (facetIndex 11), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 49), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0102_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0102 = true := by
  decide +kernel
theorem leaf0102_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0102 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0102_counts_checked
def leaf0103 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 11), (facetIndex 13), (facetIndex 14), (facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 54), (facetIndex 61), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0103_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0103 = true := by
  decide +kernel
theorem leaf0103_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0103 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0103_counts_checked
def leaf0104 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 12), (facetIndex 13), (facetIndex 14), (facetIndex 24), (facetIndex 25), (facetIndex 36), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0104_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0104 = true := by
  decide +kernel
theorem leaf0104_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0104 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0104_counts_checked
def leaf0105 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 23), (facetIndex 27), (facetIndex 35), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0105_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0105 = true := by
  decide +kernel
theorem leaf0105_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0105 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0105_counts_checked
def leaf0106 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 23), (facetIndex 26), (facetIndex 36), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0106_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0106 = true := by
  decide +kernel
theorem leaf0106_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0106 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0106_counts_checked
def leaf0107 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 14), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 52), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0107_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0107 = true := by
  decide +kernel
theorem leaf0107_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0107 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0107_counts_checked
def leaf0108 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 12), (facetIndex 19), (facetIndex 20), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0108_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0108 = true := by
  decide +kernel
theorem leaf0108_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0108 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0108_counts_checked
def leaf0109 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0109_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0109 = true := by
  decide +kernel
theorem leaf0109_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0109 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0109_counts_checked
def leaf0110 : List (Fin data.count) := [(facetIndex 11), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 19), (facetIndex 24), (facetIndex 27), (facetIndex 36), (facetIndex 49), (facetIndex 54), (facetIndex 61), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0110_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0110 = true := by
  decide +kernel
theorem leaf0110_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0110 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0110_counts_checked
def leaf0111 : List (Fin data.count) := [(facetIndex 12), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 17), (facetIndex 24), (facetIndex 27), (facetIndex 36), (facetIndex 46), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0111_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0111 = true := by
  decide +kernel
theorem leaf0111_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0111 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0111_counts_checked
def leaf0112 : List (Fin data.count) := [(facetIndex 6), (facetIndex 8), (facetIndex 9), (facetIndex 16), (facetIndex 20), (facetIndex 23), (facetIndex 27), (facetIndex 36), (facetIndex 59), (facetIndex 68), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0112_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0112 = true := by
  decide +kernel
theorem leaf0112_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0112 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0112_counts_checked
def leaf0113 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 9), (facetIndex 16), (facetIndex 18), (facetIndex 23), (facetIndex 27), (facetIndex 36), (facetIndex 54), (facetIndex 65), (facetIndex 78), (facetIndex 80), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0113_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0113 = true := by
  decide +kernel
theorem leaf0113_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0113 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0113_counts_checked
def leaf0114 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 13), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 26), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0114_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0114 = true := by
  decide +kernel
theorem leaf0114_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0114 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0114_counts_checked
def leaf0115 : List (Fin data.count) := [(facetIndex 3), (facetIndex 9), (facetIndex 13), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 34), (facetIndex 45), (facetIndex 52), (facetIndex 53), (facetIndex 68), (facetIndex 73), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0115_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0115 = true := by
  decide +kernel
theorem leaf0115_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0115 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0115_counts_checked
def leaf0116 : List (Fin data.count) := [(facetIndex 4), (facetIndex 8), (facetIndex 14), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 25), (facetIndex 43), (facetIndex 52), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0116_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0116 = true := by
  decide +kernel
theorem leaf0116_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0116 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0116_counts_checked
def leaf0117 : List (Fin data.count) := [(facetIndex 3), (facetIndex 9), (facetIndex 15), (facetIndex 17), (facetIndex 20), (facetIndex 23), (facetIndex 26), (facetIndex 36), (facetIndex 53), (facetIndex 59), (facetIndex 68), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0117_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0117 = true := by
  decide +kernel
theorem leaf0117_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0117 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0117_counts_checked
def leaf0118 : List (Fin data.count) := [(facetIndex 4), (facetIndex 8), (facetIndex 15), (facetIndex 18), (facetIndex 19), (facetIndex 23), (facetIndex 27), (facetIndex 35), (facetIndex 54), (facetIndex 58), (facetIndex 65), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0118_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0118 = true := by
  decide +kernel
theorem leaf0118_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0118 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0118_counts_checked
def leaf0119 : List (Fin data.count) := [(facetIndex 3), (facetIndex 14), (facetIndex 16), (facetIndex 18), (facetIndex 19), (facetIndex 24), (facetIndex 25), (facetIndex 36), (facetIndex 49), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0119_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0119 = true := by
  decide +kernel
theorem leaf0119_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0119 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0119_counts_checked
def leaf0120 : List (Fin data.count) := [(facetIndex 4), (facetIndex 13), (facetIndex 16), (facetIndex 17), (facetIndex 20), (facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 46), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0120_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0120 = true := by
  decide +kernel
theorem leaf0120_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0120 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0120_counts_checked
def leaf0121 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 95), (facetIndex 96)]
theorem leaf0121_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0121 = true := by
  decide +kernel
theorem leaf0121_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0121 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0121_counts_checked
def leaf0122 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 20), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 95), (facetIndex 96)]
theorem leaf0122_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0122 = true := by
  decide +kernel
theorem leaf0122_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0122 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0122_counts_checked
def leaf0123 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 95), (facetIndex 96)]
theorem leaf0123_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0123 = true := by
  decide +kernel
theorem leaf0123_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0123 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0123_counts_checked
def leaf0124 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 13), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 95), (facetIndex 96)]
theorem leaf0124_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0124 = true := by
  decide +kernel
theorem leaf0124_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0124 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0124_counts_checked
def leaf0125 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 14), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 95), (facetIndex 96)]
theorem leaf0125_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0125 = true := by
  decide +kernel
theorem leaf0125_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0125 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0125_counts_checked
def leaf0126 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 95), (facetIndex 96)]
theorem leaf0126_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0126 = true := by
  decide +kernel
theorem leaf0126_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0126 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0126_counts_checked
def leaf0127 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 95), (facetIndex 96)]
theorem leaf0127_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0127 = true := by
  decide +kernel
theorem leaf0127_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0127 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0127_counts_checked
def leaf0128 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 6), (facetIndex 8), (facetIndex 13), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 95), (facetIndex 96)]
theorem leaf0128_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0128 = true := by
  decide +kernel
theorem leaf0128_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0128 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0128_counts_checked
def leaf0129 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 14), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 95), (facetIndex 96)]
theorem leaf0129_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0129 = true := by
  decide +kernel
theorem leaf0129_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0129 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0129_counts_checked
def leaf0130 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 95), (facetIndex 96)]
theorem leaf0130_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0130 = true := by
  decide +kernel
theorem leaf0130_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0130 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0130_counts_checked
def leaf0131 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 11), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 95), (facetIndex 96)]
theorem leaf0131_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0131 = true := by
  decide +kernel
theorem leaf0131_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0131 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0131_counts_checked
def leaf0132 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 12), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 95), (facetIndex 96)]
theorem leaf0132_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0132 = true := by
  decide +kernel
theorem leaf0132_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0132 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0132_counts_checked
def leaf0133 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 95), (facetIndex 96)]
theorem leaf0133_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0133 = true := by
  decide +kernel
theorem leaf0133_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0133 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0133_counts_checked
def leaf0134 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 95), (facetIndex 96)]
theorem leaf0134_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0134 = true := by
  decide +kernel
theorem leaf0134_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0134 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0134_counts_checked
def leaf0135 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 4), (facetIndex 5), (facetIndex 18), (facetIndex 24), (facetIndex 25), (facetIndex 59), (facetIndex 61), (facetIndex 72), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0135_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0135 = true := by
  decide +kernel
theorem leaf0135_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0135 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0135_counts_checked
def leaf0136 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 4), (facetIndex 10), (facetIndex 19), (facetIndex 23), (facetIndex 35), (facetIndex 53), (facetIndex 58), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0136_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0136 = true := by
  decide +kernel
theorem leaf0136_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0136 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0136_counts_checked
def leaf0137 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 4), (facetIndex 10), (facetIndex 17), (facetIndex 23), (facetIndex 26), (facetIndex 53), (facetIndex 58), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0137_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0137 = true := by
  decide +kernel
theorem leaf0137_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0137 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0137_counts_checked
def leaf0138 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 14), (facetIndex 15), (facetIndex 16), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 65), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0138_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0138 = true := by
  decide +kernel
theorem leaf0138_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0138 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0138_counts_checked
def leaf0139 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 13), (facetIndex 15), (facetIndex 16), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0139_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0139 = true := by
  decide +kernel
theorem leaf0139_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0139 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0139_counts_checked
def leaf0140 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 10), (facetIndex 15), (facetIndex 16), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 46), (facetIndex 59), (facetIndex 72), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0140_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0140 = true := by
  decide +kernel
theorem leaf0140_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0140 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0140_counts_checked
def leaf0141 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 10), (facetIndex 15), (facetIndex 16), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 73), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0141_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0141 = true := by
  decide +kernel
theorem leaf0141_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0141 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0141_counts_checked
def leaf0142 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 8), (facetIndex 15), (facetIndex 18), (facetIndex 21), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0142_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0142 = true := by
  decide +kernel
theorem leaf0142_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0142 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0142_counts_checked
def leaf0143 : List (Fin data.count) := [(facetIndex 1), (facetIndex 4), (facetIndex 14), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0143_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0143 = true := by
  decide +kernel
theorem leaf0143_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0143 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0143_counts_checked
def leaf0144 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 13), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 45), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0144_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0144 = true := by
  decide +kernel
theorem leaf0144_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0144 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0144_counts_checked
def leaf0145 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 14), (facetIndex 16), (facetIndex 18), (facetIndex 24), (facetIndex 25), (facetIndex 36), (facetIndex 59), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0145_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0145 = true := by
  decide +kernel
theorem leaf0145_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0145 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0145_counts_checked
def leaf0146 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 13), (facetIndex 16), (facetIndex 20), (facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 54), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0146_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0146 = true := by
  decide +kernel
theorem leaf0146_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0146 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0146_counts_checked
def leaf0147 : List (Fin data.count) := [(facetIndex 3), (facetIndex 9), (facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 23), (facetIndex 26), (facetIndex 36), (facetIndex 53), (facetIndex 59), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0147_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0147 = true := by
  decide +kernel
theorem leaf0147_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0147 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0147_counts_checked
def leaf0148 : List (Fin data.count) := [(facetIndex 4), (facetIndex 8), (facetIndex 10), (facetIndex 15), (facetIndex 19), (facetIndex 23), (facetIndex 27), (facetIndex 35), (facetIndex 54), (facetIndex 58), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0148_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0148 = true := by
  decide +kernel
theorem leaf0148_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0148 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0148_counts_checked
def leaf0149 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 13), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0149_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0149 = true := by
  decide +kernel
theorem leaf0149_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0149 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0149_counts_checked
def leaf0150 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 12), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 46), (facetIndex 59), (facetIndex 70), (facetIndex 72), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0150_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0150 = true := by
  decide +kernel
theorem leaf0150_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0150 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0150_counts_checked
def leaf0151 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 11), (facetIndex 15), (facetIndex 18), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 70), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0151_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0151 = true := by
  decide +kernel
theorem leaf0151_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0151 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0151_counts_checked
def leaf0152 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 11), (facetIndex 13), (facetIndex 20), (facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 54), (facetIndex 61), (facetIndex 77), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0152_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0152 = true := by
  decide +kernel
theorem leaf0152_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0152 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0152_counts_checked
def leaf0153 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 12), (facetIndex 14), (facetIndex 18), (facetIndex 24), (facetIndex 25), (facetIndex 36), (facetIndex 59), (facetIndex 61), (facetIndex 72), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0153_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0153 = true := by
  decide +kernel
theorem leaf0153_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0153 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0153_counts_checked
def leaf0154 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 8), (facetIndex 10), (facetIndex 19), (facetIndex 23), (facetIndex 27), (facetIndex 35), (facetIndex 58), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0154_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0154 = true := by
  decide +kernel
theorem leaf0154_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0154 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0154_counts_checked
def leaf0155 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 9), (facetIndex 10), (facetIndex 17), (facetIndex 23), (facetIndex 26), (facetIndex 36), (facetIndex 53), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0155_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0155 = true := by
  decide +kernel
theorem leaf0155_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0155 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0155_counts_checked
def leaf0156 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 9), (facetIndex 15), (facetIndex 24), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 72), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0156_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0156 = true := by
  decide +kernel
theorem leaf0156_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0156 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0156_counts_checked
def leaf0157 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 13), (facetIndex 16), (facetIndex 23), (facetIndex 45), (facetIndex 53), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0157_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0157 = true := by
  decide +kernel
theorem leaf0157_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0157 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0157_counts_checked
def leaf0158 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 14), (facetIndex 16), (facetIndex 23), (facetIndex 43), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0158_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0158 = true := by
  decide +kernel
theorem leaf0158_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0158 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0158_counts_checked
def leaf0159 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0159_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0159 = true := by
  decide +kernel
theorem leaf0159_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0159 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0159_counts_checked
def leaf0160 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 19), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0160_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0160 = true := by
  decide +kernel
theorem leaf0160_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0160 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0160_counts_checked
def leaf0161 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 18), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 59), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0161_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0161 = true := by
  decide +kernel
theorem leaf0161_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0161 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0161_counts_checked
def leaf0162 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 20), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 54), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0162_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0162 = true := by
  decide +kernel
theorem leaf0162_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0162 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0162_counts_checked
def leaf0163 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 9), (facetIndex 15), (facetIndex 24), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 72), (facetIndex 77), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0163_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0163 = true := by
  decide +kernel
theorem leaf0163_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0163 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0163_counts_checked
def leaf0164 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 13), (facetIndex 16), (facetIndex 23), (facetIndex 45), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0164_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0164 = true := by
  decide +kernel
theorem leaf0164_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0164 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0164_counts_checked
def leaf0165 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 14), (facetIndex 16), (facetIndex 23), (facetIndex 43), (facetIndex 53), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0165_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0165 = true := by
  decide +kernel
theorem leaf0165_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0165 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0165_counts_checked
def leaf0166 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 59), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0166_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0166 = true := by
  decide +kernel
theorem leaf0166_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0166 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0166_counts_checked
def leaf0167 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 19), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 54), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0167_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0167 = true := by
  decide +kernel
theorem leaf0167_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0167 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0167_counts_checked
def leaf0168 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 18), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 78), (facetIndex 80), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0168_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0168 = true := by
  decide +kernel
theorem leaf0168_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0168 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0168_counts_checked
def leaf0169 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 20), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 73), (facetIndex 80), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0169_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0169 = true := by
  decide +kernel
theorem leaf0169_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0169 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0169_counts_checked
def leaf0170 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 8), (facetIndex 13), (facetIndex 16), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0170_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0170 = true := by
  decide +kernel
theorem leaf0170_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0170 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0170_counts_checked
def leaf0171 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 12), (facetIndex 14), (facetIndex 15), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 72), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0171_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0171 = true := by
  decide +kernel
theorem leaf0171_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0171 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0171_counts_checked
def leaf0172 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 11), (facetIndex 13), (facetIndex 15), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0172_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0172 = true := by
  decide +kernel
theorem leaf0172_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0172 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0172_counts_checked
def leaf0173 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 11), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 80), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0173_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0173 = true := by
  decide +kernel
theorem leaf0173_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0173 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0173_counts_checked
def leaf0174 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 12), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 80), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0174_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0174 = true := by
  decide +kernel
theorem leaf0174_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0174 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0174_counts_checked
def leaf0175 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0175_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0175 = true := by
  decide +kernel
theorem leaf0175_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0175 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0175_counts_checked
def leaf0176 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0176_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0176 = true := by
  decide +kernel
theorem leaf0176_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0176 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0176_counts_checked
def leaf0177 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 8), (facetIndex 13), (facetIndex 16), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0177_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0177 = true := by
  decide +kernel
theorem leaf0177_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0177 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0177_counts_checked
def leaf0178 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 12), (facetIndex 14), (facetIndex 15), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 72), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0178_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0178 = true := by
  decide +kernel
theorem leaf0178_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0178 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0178_counts_checked
def leaf0179 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 11), (facetIndex 13), (facetIndex 15), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 77), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0179_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0179 = true := by
  decide +kernel
theorem leaf0179_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0179 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0179_counts_checked
def leaf0180 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 11), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 54), (facetIndex 61), (facetIndex 70), (facetIndex 77), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0180_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0180 = true := by
  decide +kernel
theorem leaf0180_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0180 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0180_counts_checked
def leaf0181 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 12), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 59), (facetIndex 61), (facetIndex 70), (facetIndex 72), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0181_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0181 = true := by
  decide +kernel
theorem leaf0181_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0181 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0181_counts_checked
def leaf0182 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 52), (facetIndex 58), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0182_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0182 = true := by
  decide +kernel
theorem leaf0182_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0182 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0182_counts_checked
def leaf0183 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0183_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0183 = true := by
  decide +kernel
theorem leaf0183_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0183 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0183_counts_checked
def leaf0184 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 8), (facetIndex 13), (facetIndex 16), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 49), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0184_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0184 = true := by
  decide +kernel
theorem leaf0184_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0184 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0184_counts_checked
def leaf0185 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 12), (facetIndex 14), (facetIndex 15), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 65), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0185_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0185 = true := by
  decide +kernel
theorem leaf0185_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0185 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0185_counts_checked
def leaf0186 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 11), (facetIndex 13), (facetIndex 15), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 68), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0186_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0186 = true := by
  decide +kernel
theorem leaf0186_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0186 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0186_counts_checked
def leaf0187 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 11), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 25), (facetIndex 43), (facetIndex 59), (facetIndex 61), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0187_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0187 = true := by
  decide +kernel
theorem leaf0187_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0187 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0187_counts_checked
def leaf0188 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 12), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 34), (facetIndex 45), (facetIndex 54), (facetIndex 61), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0188_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0188 = true := by
  decide +kernel
theorem leaf0188_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0188 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0188_counts_checked
def leaf0189 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 26), (facetIndex 42), (facetIndex 52), (facetIndex 58), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0189_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0189 = true := by
  decide +kernel
theorem leaf0189_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0189 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0189_counts_checked
def leaf0190 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 35), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0190_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0190 = true := by
  decide +kernel
theorem leaf0190_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0190 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0190_counts_checked
def leaf0191 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 15), (facetIndex 16), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0191_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0191 = true := by
  decide +kernel
theorem leaf0191_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0191 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0191_counts_checked
def leaf0192 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 15), (facetIndex 16), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 72), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0192_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0192 = true := by
  decide +kernel
theorem leaf0192_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0192 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0192_counts_checked
def leaf0193 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 15), (facetIndex 16), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 73), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0193_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0193 = true := by
  decide +kernel
theorem leaf0193_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0193 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0193_counts_checked
def leaf0194 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 5), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 34), (facetIndex 54), (facetIndex 61), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0194_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0194 = true := by
  decide +kernel
theorem leaf0194_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0194 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0194_counts_checked
def leaf0195 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 5), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 25), (facetIndex 59), (facetIndex 61), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0195_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0195 = true := by
  decide +kernel
theorem leaf0195_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0195 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0195_counts_checked
def leaf0196 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 35), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0196_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0196 = true := by
  decide +kernel
theorem leaf0196_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0196 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0196_counts_checked
def leaf0197 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 26), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0197_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0197 = true := by
  decide +kernel
theorem leaf0197_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0197 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0197_counts_checked
def leaf0198 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 6), (facetIndex 8), (facetIndex 13), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 97), (facetIndex 98)]
theorem leaf0198_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0198 = true := by
  decide +kernel
theorem leaf0198_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0198 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0198_counts_checked
def leaf0199 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 14), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 97), (facetIndex 98)]
theorem leaf0199_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0199 = true := by
  decide +kernel
theorem leaf0199_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0199 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0199_counts_checked
def leaf0200 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 97), (facetIndex 98)]
theorem leaf0200_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0200 = true := by
  decide +kernel
theorem leaf0200_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0200 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0200_counts_checked
def leaf0201 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 11), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0201_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0201 = true := by
  decide +kernel
theorem leaf0201_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0201 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0201_counts_checked
def leaf0202 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 12), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0202_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0202 = true := by
  decide +kernel
theorem leaf0202_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0202 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0202_counts_checked
def leaf0203 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0203_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0203 = true := by
  decide +kernel
theorem leaf0203_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0203 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0203_counts_checked
def leaf0204 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0204_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0204 = true := by
  decide +kernel
theorem leaf0204_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0204 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0204_counts_checked
def leaf0205 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 97), (facetIndex 98)]
theorem leaf0205_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0205 = true := by
  decide +kernel
theorem leaf0205_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0205 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0205_counts_checked
def leaf0206 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 20), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 97), (facetIndex 98)]
theorem leaf0206_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0206 = true := by
  decide +kernel
theorem leaf0206_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0206 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0206_counts_checked
def leaf0207 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 97), (facetIndex 98)]
theorem leaf0207_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0207 = true := by
  decide +kernel
theorem leaf0207_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0207 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0207_counts_checked
def leaf0208 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 13), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0208_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0208 = true := by
  decide +kernel
theorem leaf0208_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0208 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0208_counts_checked
def leaf0209 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 14), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0209_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0209 = true := by
  decide +kernel
theorem leaf0209_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0209 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0209_counts_checked
def leaf0210 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0210_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0210 = true := by
  decide +kernel
theorem leaf0210_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0210 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0210_counts_checked
def leaf0211 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0211_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0211 = true := by
  decide +kernel
theorem leaf0211_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0211 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0211_counts_checked
def leaf0212 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 18), (facetIndex 19), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0212_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0212 = true := by
  decide +kernel
theorem leaf0212_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0212 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0212_counts_checked
def leaf0213 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 18), (facetIndex 19), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0213_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0213 = true := by
  decide +kernel
theorem leaf0213_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0213 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0213_counts_checked
def leaf0214 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 17), (facetIndex 20), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0214_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0214 = true := by
  decide +kernel
theorem leaf0214_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0214 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0214_counts_checked
def leaf0215 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 14), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 35), (facetIndex 41), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0215_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0215 = true := by
  decide +kernel
theorem leaf0215_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0215 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0215_counts_checked
def leaf0216 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 13), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 26), (facetIndex 41), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0216_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0216 = true := by
  decide +kernel
theorem leaf0216_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0216 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0216_counts_checked
def leaf0217 : List (Fin data.count) := [(facetIndex 9), (facetIndex 10), (facetIndex 13), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 34), (facetIndex 41), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0217_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0217 = true := by
  decide +kernel
theorem leaf0217_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0217 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0217_counts_checked
def leaf0218 : List (Fin data.count) := [(facetIndex 8), (facetIndex 10), (facetIndex 14), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 25), (facetIndex 41), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0218_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0218 = true := by
  decide +kernel
theorem leaf0218_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0218 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0218_counts_checked
def leaf0219 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0219_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0219 = true := by
  decide +kernel
theorem leaf0219_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0219 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0219_counts_checked
def leaf0220 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 20), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0220_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0220 = true := by
  decide +kernel
theorem leaf0220_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0220 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0220_counts_checked
def leaf0221 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0221_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0221 = true := by
  decide +kernel
theorem leaf0221_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0221 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0221_counts_checked
def leaf0222 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 13), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 97), (facetIndex 98)]
theorem leaf0222_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0222 = true := by
  decide +kernel
theorem leaf0222_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0222 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0222_counts_checked
def leaf0223 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 14), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 97), (facetIndex 98)]
theorem leaf0223_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0223 = true := by
  decide +kernel
theorem leaf0223_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0223 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0223_counts_checked
def leaf0224 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 97), (facetIndex 98)]
theorem leaf0224_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0224 = true := by
  decide +kernel
theorem leaf0224_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0224 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0224_counts_checked
def leaf0225 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 97), (facetIndex 98)]
theorem leaf0225_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0225 = true := by
  decide +kernel
theorem leaf0225_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0225 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0225_counts_checked
def leaf0226 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 6), (facetIndex 8), (facetIndex 13), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0226_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0226 = true := by
  decide +kernel
theorem leaf0226_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0226 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0226_counts_checked
def leaf0227 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 14), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0227_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0227 = true := by
  decide +kernel
theorem leaf0227_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0227 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0227_counts_checked
def leaf0228 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0228_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0228 = true := by
  decide +kernel
theorem leaf0228_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0228 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0228_counts_checked
def leaf0229 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 11), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 97), (facetIndex 98)]
theorem leaf0229_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0229 = true := by
  decide +kernel
theorem leaf0229_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0229 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0229_counts_checked
def leaf0230 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 12), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 97), (facetIndex 98)]
theorem leaf0230_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0230 = true := by
  decide +kernel
theorem leaf0230_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0230 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0230_counts_checked
def leaf0231 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 97), (facetIndex 98)]
theorem leaf0231_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0231 = true := by
  decide +kernel
theorem leaf0231_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0231 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0231_counts_checked
def leaf0232 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 10), (facetIndex 17), (facetIndex 19), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 97), (facetIndex 98)]
theorem leaf0232_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0232 = true := by
  decide +kernel
theorem leaf0232_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0232 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0232_counts_checked
def leaf0233 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 8), (facetIndex 14), (facetIndex 17), (facetIndex 24), (facetIndex 25), (facetIndex 41), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0233_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0233 = true := by
  decide +kernel
theorem leaf0233_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0233 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0233_counts_checked
def leaf0234 : List (Fin data.count) := [(facetIndex 1), (facetIndex 8), (facetIndex 10), (facetIndex 14), (facetIndex 20), (facetIndex 23), (facetIndex 35), (facetIndex 41), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0234_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0234 = true := by
  decide +kernel
theorem leaf0234_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0234 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0234_counts_checked
def leaf0235 : List (Fin data.count) := [(facetIndex 2), (facetIndex 9), (facetIndex 10), (facetIndex 13), (facetIndex 18), (facetIndex 23), (facetIndex 26), (facetIndex 41), (facetIndex 53), (facetIndex 59), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0235_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0235 = true := by
  decide +kernel
theorem leaf0235_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0235 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0235_counts_checked
def leaf0236 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 13), (facetIndex 18), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0236_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0236 = true := by
  decide +kernel
theorem leaf0236_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0236 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0236_counts_checked
def leaf0237 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 14), (facetIndex 17), (facetIndex 20), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 68), (facetIndex 73), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0237_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0237 = true := by
  decide +kernel
theorem leaf0237_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0237 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0237_counts_checked
def leaf0238 : List (Fin data.count) := [(facetIndex 1), (facetIndex 8), (facetIndex 10), (facetIndex 17), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0238_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0238 = true := by
  decide +kernel
theorem leaf0238_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0238 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0238_counts_checked
def leaf0239 : List (Fin data.count) := [(facetIndex 2), (facetIndex 9), (facetIndex 10), (facetIndex 18), (facetIndex 19), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 49), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0239_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0239 = true := by
  decide +kernel
theorem leaf0239_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0239 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0239_counts_checked
def leaf0240 : List (Fin data.count) := [(facetIndex 2), (facetIndex 9), (facetIndex 13), (facetIndex 18), (facetIndex 20), (facetIndex 23), (facetIndex 26), (facetIndex 41), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0240_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0240 = true := by
  decide +kernel
theorem leaf0240_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0240 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0240_counts_checked
def leaf0241 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 13), (facetIndex 17), (facetIndex 19), (facetIndex 24), (facetIndex 34), (facetIndex 41), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0241_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0241 = true := by
  decide +kernel
theorem leaf0241_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0241 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0241_counts_checked
def leaf0242 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 14), (facetIndex 17), (facetIndex 19), (facetIndex 24), (facetIndex 25), (facetIndex 41), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0242_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0242 = true := by
  decide +kernel
theorem leaf0242_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0242 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0242_counts_checked
def leaf0243 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 14), (facetIndex 17), (facetIndex 20), (facetIndex 21), (facetIndex 36), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 68), (facetIndex 73), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0243_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0243 = true := by
  decide +kernel
theorem leaf0243_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0243 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0243_counts_checked
def leaf0244 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 13), (facetIndex 18), (facetIndex 19), (facetIndex 22), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0244_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0244 = true := by
  decide +kernel
theorem leaf0244_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0244 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0244_counts_checked
def leaf0245 : List (Fin data.count) := [(facetIndex 9), (facetIndex 10), (facetIndex 14), (facetIndex 18), (facetIndex 19), (facetIndex 21), (facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 72), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0245_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0245 = true := by
  decide +kernel
theorem leaf0245_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0245 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0245_counts_checked
def leaf0246 : List (Fin data.count) := [(facetIndex 8), (facetIndex 10), (facetIndex 13), (facetIndex 17), (facetIndex 20), (facetIndex 22), (facetIndex 27), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0246_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0246 = true := by
  decide +kernel
theorem leaf0246_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0246 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0246_counts_checked
def leaf0247 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 9), (facetIndex 15), (facetIndex 18), (facetIndex 21), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0247_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0247 = true := by
  decide +kernel
theorem leaf0247_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0247 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0247_counts_checked
def leaf0248 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 13), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 45), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0248_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0248 = true := by
  decide +kernel
theorem leaf0248_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0248 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0248_counts_checked
def leaf0249 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 14), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 68), (facetIndex 73), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0249_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0249 = true := by
  decide +kernel
theorem leaf0249_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0249 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0249_counts_checked
def leaf0250 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 14), (facetIndex 15), (facetIndex 17), (facetIndex 24), (facetIndex 25), (facetIndex 36), (facetIndex 59), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0250_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0250 = true := by
  decide +kernel
theorem leaf0250_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0250 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0250_counts_checked
def leaf0251 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 13), (facetIndex 15), (facetIndex 19), (facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 54), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0251_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0251 = true := by
  decide +kernel
theorem leaf0251_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0251 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0251_counts_checked
def leaf0252 : List (Fin data.count) := [(facetIndex 3), (facetIndex 9), (facetIndex 10), (facetIndex 16), (facetIndex 18), (facetIndex 23), (facetIndex 26), (facetIndex 36), (facetIndex 53), (facetIndex 59), (facetIndex 78), (facetIndex 80), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0252_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0252 = true := by
  decide +kernel
theorem leaf0252_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0252 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0252_counts_checked
def leaf0253 : List (Fin data.count) := [(facetIndex 4), (facetIndex 8), (facetIndex 10), (facetIndex 16), (facetIndex 20), (facetIndex 23), (facetIndex 27), (facetIndex 35), (facetIndex 54), (facetIndex 58), (facetIndex 73), (facetIndex 80), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0253_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0253 = true := by
  decide +kernel
theorem leaf0253_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0253 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0253_counts_checked
def leaf0254 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 14), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 68), (facetIndex 73), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0254_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0254 = true := by
  decide +kernel
theorem leaf0254_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0254 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0254_counts_checked
def leaf0255 : List (Fin data.count) := [(facetIndex 1), (facetIndex 8), (facetIndex 11), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0255_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0255 = true := by
  decide +kernel
theorem leaf0255_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0255 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0255_counts_checked
def leaf0256 : List (Fin data.count) := [(facetIndex 2), (facetIndex 9), (facetIndex 12), (facetIndex 15), (facetIndex 18), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 49), (facetIndex 54), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0256_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0256 = true := by
  decide +kernel
theorem leaf0256_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0256 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0256_counts_checked
def leaf0257 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 6), (facetIndex 13), (facetIndex 19), (facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0257_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0257 = true := by
  decide +kernel
theorem leaf0257_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0257 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0257_counts_checked
def leaf0258 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 7), (facetIndex 14), (facetIndex 17), (facetIndex 24), (facetIndex 25), (facetIndex 36), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0258_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0258 = true := by
  decide +kernel
theorem leaf0258_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0258 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0258_counts_checked
def leaf0259 : List (Fin data.count) := [(facetIndex 4), (facetIndex 8), (facetIndex 10), (facetIndex 11), (facetIndex 20), (facetIndex 23), (facetIndex 27), (facetIndex 35), (facetIndex 54), (facetIndex 58), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0259_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0259 = true := by
  decide +kernel
theorem leaf0259_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0259 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0259_counts_checked
def leaf0260 : List (Fin data.count) := [(facetIndex 3), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 18), (facetIndex 23), (facetIndex 26), (facetIndex 36), (facetIndex 53), (facetIndex 59), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0260_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0260 = true := by
  decide +kernel
theorem leaf0260_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0260 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0260_counts_checked
def leaf0261 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 14), (facetIndex 15), (facetIndex 18), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0261_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0261 = true := by
  decide +kernel
theorem leaf0261_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0261 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0261_counts_checked
def leaf0262 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 13), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0262_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0262 = true := by
  decide +kernel
theorem leaf0262_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0262 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0262_counts_checked
def leaf0263 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 68), (facetIndex 73), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0263_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0263 = true := by
  decide +kernel
theorem leaf0263_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0263 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0263_counts_checked
def leaf0264 : List (Fin data.count) := [(facetIndex 3), (facetIndex 14), (facetIndex 15), (facetIndex 17), (facetIndex 19), (facetIndex 24), (facetIndex 25), (facetIndex 36), (facetIndex 49), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0264_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0264 = true := by
  decide +kernel
theorem leaf0264_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0264 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0264_counts_checked
def leaf0265 : List (Fin data.count) := [(facetIndex 4), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 19), (facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 46), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0265_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0265 = true := by
  decide +kernel
theorem leaf0265_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0265 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0265_counts_checked
def leaf0266 : List (Fin data.count) := [(facetIndex 3), (facetIndex 9), (facetIndex 16), (facetIndex 18), (facetIndex 20), (facetIndex 23), (facetIndex 26), (facetIndex 36), (facetIndex 53), (facetIndex 59), (facetIndex 68), (facetIndex 80), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0266_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0266 = true := by
  decide +kernel
theorem leaf0266_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0266 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0266_counts_checked
def leaf0267 : List (Fin data.count) := [(facetIndex 4), (facetIndex 8), (facetIndex 16), (facetIndex 18), (facetIndex 20), (facetIndex 23), (facetIndex 27), (facetIndex 35), (facetIndex 54), (facetIndex 58), (facetIndex 65), (facetIndex 80), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0267_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0267 = true := by
  decide +kernel
theorem leaf0267_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0267 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0267_counts_checked
def leaf0268 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 13), (facetIndex 17), (facetIndex 19), (facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 52), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0268_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0268 = true := by
  decide +kernel
theorem leaf0268_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0268 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0268_counts_checked
def leaf0269 : List (Fin data.count) := [(facetIndex 3), (facetIndex 9), (facetIndex 12), (facetIndex 18), (facetIndex 20), (facetIndex 23), (facetIndex 26), (facetIndex 36), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 80), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0269_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0269 = true := by
  decide +kernel
theorem leaf0269_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0269 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0269_counts_checked
def leaf0270 : List (Fin data.count) := [(facetIndex 4), (facetIndex 8), (facetIndex 11), (facetIndex 18), (facetIndex 20), (facetIndex 23), (facetIndex 27), (facetIndex 35), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 80), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0270_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0270 = true := by
  decide +kernel
theorem leaf0270_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0270 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0270_counts_checked
def leaf0271 : List (Fin data.count) := [(facetIndex 8), (facetIndex 11), (facetIndex 13), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 27), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0271_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0271 = true := by
  decide +kernel
theorem leaf0271_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0271 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0271_counts_checked
def leaf0272 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 14), (facetIndex 15), (facetIndex 18), (facetIndex 21), (facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0272_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0272 = true := by
  decide +kernel
theorem leaf0272_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0272 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0272_counts_checked
def leaf0273 : List (Fin data.count) := [(facetIndex 6), (facetIndex 8), (facetIndex 13), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 27), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0273_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0273 = true := by
  decide +kernel
theorem leaf0273_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0273 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0273_counts_checked
def leaf0274 : List (Fin data.count) := [(facetIndex 7), (facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 36), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 68), (facetIndex 73), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0274_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0274 = true := by
  decide +kernel
theorem leaf0274_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0274 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0274_counts_checked
def leaf0275 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 13), (facetIndex 16), (facetIndex 20), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 59), (facetIndex 61), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0275_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0275 = true := by
  decide +kernel
theorem leaf0275_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0275 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0275_counts_checked
def leaf0276 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 12), (facetIndex 15), (facetIndex 17), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0276_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0276 = true := by
  decide +kernel
theorem leaf0276_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0276 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0276_counts_checked
def leaf0277 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 11), (facetIndex 15), (facetIndex 19), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0277_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0277 = true := by
  decide +kernel
theorem leaf0277_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0277 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0277_counts_checked
def leaf0278 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 9), (facetIndex 11), (facetIndex 20), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0278_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0278 = true := by
  decide +kernel
theorem leaf0278_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0278 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0278_counts_checked
def leaf0279 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 8), (facetIndex 12), (facetIndex 18), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0279_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0279 = true := by
  decide +kernel
theorem leaf0279_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0279 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0279_counts_checked
def leaf0280 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 10), (facetIndex 14), (facetIndex 19), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0280_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0280 = true := by
  decide +kernel
theorem leaf0280_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0280 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0280_counts_checked
def leaf0281 : List (Fin data.count) := [(facetIndex 3), (facetIndex 7), (facetIndex 10), (facetIndex 13), (facetIndex 17), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 77), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0281_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0281 = true := by
  decide +kernel
theorem leaf0281_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0281 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0281_counts_checked
def leaf0282 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 7), (facetIndex 8), (facetIndex 11), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0282_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0282 = true := by
  decide +kernel
theorem leaf0282_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0282 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0282_counts_checked
def leaf0283 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 14), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 54), (facetIndex 61), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0283_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0283 = true := by
  decide +kernel
theorem leaf0283_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0283 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0283_counts_checked
def leaf0284 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 10), (facetIndex 12), (facetIndex 13), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0284_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0284 = true := by
  decide +kernel
theorem leaf0284_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0284 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0284_counts_checked
def leaf0285 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 6), (facetIndex 12), (facetIndex 18), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0285_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0285 = true := by
  decide +kernel
theorem leaf0285_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0285 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0285_counts_checked
def leaf0286 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 7), (facetIndex 11), (facetIndex 20), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0286_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0286 = true := by
  decide +kernel
theorem leaf0286_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0286 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0286_counts_checked
def leaf0287 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 17), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 77), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0287_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0287 = true := by
  decide +kernel
theorem leaf0287_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0287 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0287_counts_checked
def leaf0288 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 10), (facetIndex 12), (facetIndex 19), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0288_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0288 = true := by
  decide +kernel
theorem leaf0288_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0288 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0288_counts_checked
def leaf0289 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 61), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0289_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0289 = true := by
  decide +kernel
theorem leaf0289_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0289 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0289_counts_checked
def leaf0290 : List (Fin data.count) := [(facetIndex 1), (facetIndex 9), (facetIndex 11), (facetIndex 15), (facetIndex 19), (facetIndex 24), (facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0290_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0290 = true := by
  decide +kernel
theorem leaf0290_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0290 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0290_counts_checked
def leaf0291 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 12), (facetIndex 15), (facetIndex 17), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0291_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0291 = true := by
  decide +kernel
theorem leaf0291_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0291 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0291_counts_checked
def leaf0292 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 6), (facetIndex 14), (facetIndex 20), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0292_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0292 = true := by
  decide +kernel
theorem leaf0292_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0292 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0292_counts_checked
def leaf0293 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 7), (facetIndex 13), (facetIndex 18), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0293_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0293 = true := by
  decide +kernel
theorem leaf0293_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0293 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0293_counts_checked
def leaf0294 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 11), (facetIndex 19), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0294_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0294 = true := by
  decide +kernel
theorem leaf0294_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0294 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0294_counts_checked
def leaf0295 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 10), (facetIndex 12), (facetIndex 17), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0295_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0295 = true := by
  decide +kernel
theorem leaf0295_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0295 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0295_counts_checked
def leaf0296 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 6), (facetIndex 8), (facetIndex 12), (facetIndex 24), (facetIndex 27), (facetIndex 44), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0296_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0296 = true := by
  decide +kernel
theorem leaf0296_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0296 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0296_counts_checked
def leaf0297 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 10), (facetIndex 12), (facetIndex 14), (facetIndex 23), (facetIndex 36), (facetIndex 43), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0297_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0297 = true := by
  decide +kernel
theorem leaf0297_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0297 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0297_counts_checked
def leaf0298 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 23), (facetIndex 27), (facetIndex 45), (facetIndex 54), (facetIndex 61), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0298_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0298 = true := by
  decide +kernel
theorem leaf0298_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0298 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0298_counts_checked
def leaf0299 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 7), (facetIndex 11), (facetIndex 18), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0299_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0299 = true := by
  decide +kernel
theorem leaf0299_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0299 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0299_counts_checked
def leaf0300 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 6), (facetIndex 12), (facetIndex 20), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0300_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0300 = true := by
  decide +kernel
theorem leaf0300_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0300 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0300_counts_checked
def leaf0301 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 10), (facetIndex 12), (facetIndex 17), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0301_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0301 = true := by
  decide +kernel
theorem leaf0301_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0301 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0301_counts_checked
def leaf0302 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 19), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0302_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0302 = true := by
  decide +kernel
theorem leaf0302_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0302 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0302_counts_checked
def leaf0303 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 3), (facetIndex 8), (facetIndex 17), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 68), (facetIndex 72), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0303_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0303 = true := by
  decide +kernel
theorem leaf0303_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0303 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0303_counts_checked
def leaf0304 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 4), (facetIndex 14), (facetIndex 20), (facetIndex 35), (facetIndex 42), (facetIndex 46), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0304_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0304 = true := by
  decide +kernel
theorem leaf0304_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0304 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0304_counts_checked
def leaf0305 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 3), (facetIndex 13), (facetIndex 18), (facetIndex 26), (facetIndex 44), (facetIndex 49), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0305_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0305 = true := by
  decide +kernel
theorem leaf0305_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0305 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0305_counts_checked
def leaf0306 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 13), (facetIndex 16), (facetIndex 18), (facetIndex 27), (facetIndex 34), (facetIndex 45), (facetIndex 54), (facetIndex 61), (facetIndex 65), (facetIndex 78), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0306_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0306 = true := by
  decide +kernel
theorem leaf0306_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0306 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0306_counts_checked
def leaf0307 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 14), (facetIndex 16), (facetIndex 20), (facetIndex 25), (facetIndex 36), (facetIndex 43), (facetIndex 59), (facetIndex 61), (facetIndex 68), (facetIndex 73), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0307_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0307 = true := by
  decide +kernel
theorem leaf0307_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0307 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0307_counts_checked
def leaf0308 : List (Fin data.count) := [(facetIndex 0), (facetIndex 8), (facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 27), (facetIndex 35), (facetIndex 44), (facetIndex 46), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0308_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0308 = true := by
  decide +kernel
theorem leaf0308_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0308 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0308_counts_checked
def leaf0309 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 15), (facetIndex 19), (facetIndex 26), (facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0309_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0309 = true := by
  decide +kernel
theorem leaf0309_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0309 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0309_counts_checked
def leaf0310 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 7), (facetIndex 19), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 65), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0310_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0310 = true := by
  decide +kernel
theorem leaf0310_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0310 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0310_counts_checked
def leaf0311 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 11), (facetIndex 18), (facetIndex 43), (facetIndex 44), (facetIndex 49), (facetIndex 53), (facetIndex 70), (facetIndex 77), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0311_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0311 = true := by
  decide +kernel
theorem leaf0311_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0311 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0311_counts_checked
def leaf0312 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 12), (facetIndex 20), (facetIndex 42), (facetIndex 45), (facetIndex 46), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0312_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0312 = true := by
  decide +kernel
theorem leaf0312_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0312 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0312_counts_checked
def leaf0313 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 6), (facetIndex 8), (facetIndex 10), (facetIndex 27), (facetIndex 35), (facetIndex 44), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0313_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0313 = true := by
  decide +kernel
theorem leaf0313_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0313 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0313_counts_checked
def leaf0314 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 7), (facetIndex 9), (facetIndex 10), (facetIndex 26), (facetIndex 36), (facetIndex 42), (facetIndex 54), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0314_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0314 = true := by
  decide +kernel
theorem leaf0314_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0314 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0314_counts_checked
def leaf0315 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 27), (facetIndex 34), (facetIndex 45), (facetIndex 54), (facetIndex 61), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0315_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0315 = true := by
  decide +kernel
theorem leaf0315_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0315 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0315_counts_checked
def leaf0316 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 10), (facetIndex 12), (facetIndex 14), (facetIndex 25), (facetIndex 36), (facetIndex 43), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0316_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0316 = true := by
  decide +kernel
theorem leaf0316_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0316 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0316_counts_checked
def leaf0317 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 5), (facetIndex 14), (facetIndex 24), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 95), (facetIndex 96)]
theorem leaf0317_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0317 = true := by
  decide +kernel
theorem leaf0317_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0317 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0317_counts_checked
def leaf0318 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 8), (facetIndex 10), (facetIndex 23), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 95), (facetIndex 96)]
theorem leaf0318_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0318 = true := by
  decide +kernel
theorem leaf0318_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0318 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0318_counts_checked
def leaf0319 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 23), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 95), (facetIndex 96)]
theorem leaf0319_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0319 = true := by
  decide +kernel
theorem leaf0319_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0319 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0319_counts_checked
def leaf0320 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 95), (facetIndex 96)]
theorem leaf0320_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0320 = true := by
  decide +kernel
theorem leaf0320_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0320 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0320_counts_checked
def leaf0321 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 95), (facetIndex 96)]
theorem leaf0321_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0321 = true := by
  decide +kernel
theorem leaf0321_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0321 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0321_counts_checked
def leaf0322 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 95), (facetIndex 96)]
theorem leaf0322_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0322 = true := by
  decide +kernel
theorem leaf0322_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0322 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0322_counts_checked
def leaf0323 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 18), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 86), (facetIndex 95), (facetIndex 96)]
theorem leaf0323_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0323 = true := by
  decide +kernel
theorem leaf0323_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0323 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0323_counts_checked
def leaf0324 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 5), (facetIndex 14), (facetIndex 24), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 97), (facetIndex 98)]
theorem leaf0324_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0324 = true := by
  decide +kernel
theorem leaf0324_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0324 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0324_counts_checked
def leaf0325 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 8), (facetIndex 10), (facetIndex 23), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 97), (facetIndex 98)]
theorem leaf0325_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0325 = true := by
  decide +kernel
theorem leaf0325_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0325 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0325_counts_checked
def leaf0326 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 23), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 97), (facetIndex 98)]
theorem leaf0326_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0326 = true := by
  decide +kernel
theorem leaf0326_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0326 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0326_counts_checked
def leaf0327 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0327_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0327 = true := by
  decide +kernel
theorem leaf0327_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0327 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0327_counts_checked
def leaf0328 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0328_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0328 = true := by
  decide +kernel
theorem leaf0328_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0328 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0328_counts_checked
def leaf0329 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0329_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0329 = true := by
  decide +kernel
theorem leaf0329_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0329 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0329_counts_checked
def leaf0330 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 18), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0330_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0330 = true := by
  decide +kernel
theorem leaf0330_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0330 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0330_counts_checked
def leaf0331 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 9), (facetIndex 15), (facetIndex 23), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 65), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0331_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0331 = true := by
  decide +kernel
theorem leaf0331_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0331 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0331_counts_checked
def leaf0332 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 13), (facetIndex 16), (facetIndex 24), (facetIndex 44), (facetIndex 49), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0332_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0332 = true := by
  decide +kernel
theorem leaf0332_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0332 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0332_counts_checked
def leaf0333 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 14), (facetIndex 16), (facetIndex 24), (facetIndex 42), (facetIndex 46), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0333_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0333 = true := by
  decide +kernel
theorem leaf0333_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0333 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0333_counts_checked
def leaf0334 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 21), (facetIndex 35), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0334_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0334 = true := by
  decide +kernel
theorem leaf0334_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0334 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0334_counts_checked
def leaf0335 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 19), (facetIndex 22), (facetIndex 26), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0335_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0335 = true := by
  decide +kernel
theorem leaf0335_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0335 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0335_counts_checked
def leaf0336 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 18), (facetIndex 21), (facetIndex 34), (facetIndex 45), (facetIndex 54), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0336_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0336 = true := by
  decide +kernel
theorem leaf0336_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0336 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0336_counts_checked
def leaf0337 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 20), (facetIndex 22), (facetIndex 25), (facetIndex 43), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 99), (facetIndex 100)]
theorem leaf0337_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0337 = true := by
  decide +kernel
theorem leaf0337_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0337 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0337_counts_checked
def leaf0338 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 8), (facetIndex 16), (facetIndex 18), (facetIndex 23), (facetIndex 27), (facetIndex 54), (facetIndex 58), (facetIndex 65), (facetIndex 78), (facetIndex 80), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0338_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0338 = true := by
  decide +kernel
theorem leaf0338_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0338 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0338_counts_checked
def leaf0339 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 14), (facetIndex 15), (facetIndex 19), (facetIndex 24), (facetIndex 36), (facetIndex 49), (facetIndex 54), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 99), (facetIndex 100)]
theorem leaf0339_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0339 = true := by
  decide +kernel
theorem leaf0339_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0339 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0339_counts_checked
def leaf0340 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 13), (facetIndex 15), (facetIndex 17), (facetIndex 24), (facetIndex 27), (facetIndex 46), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0340_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0340 = true := by
  decide +kernel
theorem leaf0340_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0340 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0340_counts_checked
def leaf0341 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 14), (facetIndex 15), (facetIndex 18), (facetIndex 21), (facetIndex 35), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0341_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0341 = true := by
  decide +kernel
theorem leaf0341_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0341 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0341_counts_checked
def leaf0342 : List (Fin data.count) := [(facetIndex 3), (facetIndex 5), (facetIndex 13), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 26), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0342_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0342 = true := by
  decide +kernel
theorem leaf0342_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0342 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0342_counts_checked
def leaf0343 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0343_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0343 = true := by
  decide +kernel
theorem leaf0343_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0343 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0343_counts_checked
def leaf0344 : List (Fin data.count) := [(facetIndex 3), (facetIndex 8), (facetIndex 10), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 25), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0344_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0344 = true := by
  decide +kernel
theorem leaf0344_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0344 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0344_counts_checked
def leaf0345 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 5), (facetIndex 8), (facetIndex 11), (facetIndex 24), (facetIndex 27), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0345_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0345 = true := by
  decide +kernel
theorem leaf0345_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0345 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0345_counts_checked
def leaf0346 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 7), (facetIndex 10), (facetIndex 14), (facetIndex 23), (facetIndex 36), (facetIndex 54), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0346_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0346 = true := by
  decide +kernel
theorem leaf0346_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0346 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0346_counts_checked
def leaf0347 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 6), (facetIndex 10), (facetIndex 13), (facetIndex 23), (facetIndex 27), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0347_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0347 = true := by
  decide +kernel
theorem leaf0347_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0347 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0347_counts_checked
def leaf0348 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 12), (facetIndex 15), (facetIndex 18), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0348_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0348 = true := by
  decide +kernel
theorem leaf0348_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0348 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0348_counts_checked
def leaf0349 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 11), (facetIndex 15), (facetIndex 20), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0349_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0349 = true := by
  decide +kernel
theorem leaf0349_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0349 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0349_counts_checked
def leaf0350 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 10), (facetIndex 16), (facetIndex 17), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0350_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0350 = true := by
  decide +kernel
theorem leaf0350_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0350 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0350_counts_checked
def leaf0351 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 10), (facetIndex 16), (facetIndex 19), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0351_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0351 = true := by
  decide +kernel
theorem leaf0351_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0351 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0351_counts_checked
def leaf0352 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 9), (facetIndex 13), (facetIndex 24), (facetIndex 41), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0352_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0352 = true := by
  decide +kernel
theorem leaf0352_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0352 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0352_counts_checked
def leaf0353 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 9), (facetIndex 10), (facetIndex 13), (facetIndex 23), (facetIndex 41), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0353_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0353 = true := by
  decide +kernel
theorem leaf0353_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0353 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0353_counts_checked
def leaf0354 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 8), (facetIndex 10), (facetIndex 14), (facetIndex 23), (facetIndex 41), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0354_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0354 = true := by
  decide +kernel
theorem leaf0354_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0354 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0354_counts_checked
def leaf0355 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 10), (facetIndex 17), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0355_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0355 = true := by
  decide +kernel
theorem leaf0355_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0355 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0355_counts_checked
def leaf0356 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 18), (facetIndex 19), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0356_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0356 = true := by
  decide +kernel
theorem leaf0356_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0356 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0356_counts_checked
def leaf0357 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 10), (facetIndex 18), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0357_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0357 = true := by
  decide +kernel
theorem leaf0357_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0357 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0357_counts_checked
def leaf0358 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 17), (facetIndex 20), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 88), (facetIndex 97), (facetIndex 98)]
theorem leaf0358_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0358 = true := by
  decide +kernel
theorem leaf0358_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0358 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0358_counts_checked
def leaf0359 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 5), (facetIndex 14), (facetIndex 24), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0359_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0359 = true := by
  decide +kernel
theorem leaf0359_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0359 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0359_counts_checked
def leaf0360 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 8), (facetIndex 10), (facetIndex 23), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0360_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0360 = true := by
  decide +kernel
theorem leaf0360_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0360 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0360_counts_checked
def leaf0361 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 23), (facetIndex 43), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0361_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0361 = true := by
  decide +kernel
theorem leaf0361_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0361 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0361_counts_checked
def leaf0362 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 97), (facetIndex 98)]
theorem leaf0362_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0362 = true := by
  decide +kernel
theorem leaf0362_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0362 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0362_counts_checked
def leaf0363 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 17), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 87), (facetIndex 97), (facetIndex 98)]
theorem leaf0363_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0363 = true := by
  decide +kernel
theorem leaf0363_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0363 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0363_counts_checked
def leaf0364 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 97), (facetIndex 98)]
theorem leaf0364_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0364 = true := by
  decide +kernel
theorem leaf0364_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0364 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0364_counts_checked
def leaf0365 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 16), (facetIndex 18), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 86), (facetIndex 97), (facetIndex 98)]
theorem leaf0365_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0365 = true := by
  decide +kernel
theorem leaf0365_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0365 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0365_counts_checked
def leaf0366 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 4), (facetIndex 5), (facetIndex 13), (facetIndex 24), (facetIndex 25), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0366_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0366 = true := by
  decide +kernel
theorem leaf0366_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0366 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0366_counts_checked
def leaf0367 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 23), (facetIndex 35), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0367_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0367 = true := by
  decide +kernel
theorem leaf0367_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0367 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0367_counts_checked
def leaf0368 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 4), (facetIndex 8), (facetIndex 10), (facetIndex 23), (facetIndex 26), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0368_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0368 = true := by
  decide +kernel
theorem leaf0368_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0368 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0368_counts_checked
def leaf0369 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 15), (facetIndex 16), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 65), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0369_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0369 = true := by
  decide +kernel
theorem leaf0369_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0369 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0369_counts_checked
def leaf0370 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 15), (facetIndex 16), (facetIndex 18), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 68), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0370_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0370 = true := by
  decide +kernel
theorem leaf0370_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0370 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0370_counts_checked
def leaf0371 : List (Fin data.count) := [(facetIndex 1), (facetIndex 10), (facetIndex 15), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 46), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0371_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0371 = true := by
  decide +kernel
theorem leaf0371_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0371 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0371_counts_checked
def leaf0372 : List (Fin data.count) := [(facetIndex 2), (facetIndex 10), (facetIndex 15), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 49), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0372_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0372 = true := by
  decide +kernel
theorem leaf0372_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0372 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0372_counts_checked
def leaf0373 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 5), (facetIndex 6), (facetIndex 13), (facetIndex 24), (facetIndex 27), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0373_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0373 = true := by
  decide +kernel
theorem leaf0373_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0373 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0373_counts_checked
def leaf0374 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 9), (facetIndex 10), (facetIndex 12), (facetIndex 23), (facetIndex 36), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0374_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0374 = true := by
  decide +kernel
theorem leaf0374_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0374 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0374_counts_checked
def leaf0375 : List (Fin data.count) := [(facetIndex 2), (facetIndex 4), (facetIndex 8), (facetIndex 10), (facetIndex 11), (facetIndex 23), (facetIndex 27), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0375_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0375 = true := by
  decide +kernel
theorem leaf0375_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0375 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0375_counts_checked
def leaf0376 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 11), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 70), (facetIndex 77), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0376_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0376 = true := by
  decide +kernel
theorem leaf0376_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0376 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0376_counts_checked
def leaf0377 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 12), (facetIndex 15), (facetIndex 18), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 70), (facetIndex 72), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0377_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0377 = true := by
  decide +kernel
theorem leaf0377_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0377 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0377_counts_checked
def leaf0378 : List (Fin data.count) := [(facetIndex 1), (facetIndex 6), (facetIndex 10), (facetIndex 16), (facetIndex 19), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 52), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0378_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0378 = true := by
  decide +kernel
theorem leaf0378_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0378 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0378_counts_checked
def leaf0379 : List (Fin data.count) := [(facetIndex 2), (facetIndex 7), (facetIndex 10), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0379_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0379 = true := by
  decide +kernel
theorem leaf0379_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0379 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0379_counts_checked
def leaf0380 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 95), (facetIndex 96)]
theorem leaf0380_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0380 = true := by
  decide +kernel
theorem leaf0380_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0380 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0380_counts_checked
def leaf0381 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 97), (facetIndex 98)]
theorem leaf0381_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0381 = true := by
  decide +kernel
theorem leaf0381_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0381 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0381_counts_checked
def leaf0382 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0382_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0382 = true := by
  decide +kernel
theorem leaf0382_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0382 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0382_counts_checked
def leaf0383 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0383_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0383 = true := by
  decide +kernel
theorem leaf0383_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0383 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0383_counts_checked
def leaf0384 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 5), (facetIndex 15), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 65), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0384_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0384 = true := by
  decide +kernel
theorem leaf0384_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0384 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0384_counts_checked
def leaf0385 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 10), (facetIndex 16), (facetIndex 43), (facetIndex 44), (facetIndex 49), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0385_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0385 = true := by
  decide +kernel
theorem leaf0385_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0385 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0385_counts_checked
def leaf0386 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 2), (facetIndex 10), (facetIndex 16), (facetIndex 42), (facetIndex 45), (facetIndex 46), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0386_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0386 = true := by
  decide +kernel
theorem leaf0386_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0386 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0386_counts_checked
def leaf0387 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 3), (facetIndex 5), (facetIndex 10), (facetIndex 35), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 73), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0387_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0387 = true := by
  decide +kernel
theorem leaf0387_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0387 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0387_counts_checked
def leaf0388 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 4), (facetIndex 5), (facetIndex 10), (facetIndex 26), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0388_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0388 = true := by
  decide +kernel
theorem leaf0388_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0388 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0388_counts_checked
def leaf0389 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 3), (facetIndex 5), (facetIndex 10), (facetIndex 34), (facetIndex 45), (facetIndex 54), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0389_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0389 = true := by
  decide +kernel
theorem leaf0389_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0389 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0389_counts_checked
def leaf0390 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 4), (facetIndex 5), (facetIndex 10), (facetIndex 25), (facetIndex 43), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0390_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0390 = true := by
  decide +kernel
theorem leaf0390_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0390 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0390_counts_checked
def leaf0391 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 5), (facetIndex 11), (facetIndex 24), (facetIndex 42), (facetIndex 54), (facetIndex 58), (facetIndex 78), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0391_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0391 = true := by
  decide +kernel
theorem leaf0391_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0391 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0391_counts_checked
def leaf0392 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 3), (facetIndex 7), (facetIndex 10), (facetIndex 23), (facetIndex 45), (facetIndex 54), (facetIndex 61), (facetIndex 72), (facetIndex 78), (facetIndex 84), (facetIndex 86), (facetIndex 99), (facetIndex 100)]
theorem leaf0392_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0392 = true := by
  decide +kernel
theorem leaf0392_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0392 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0392_counts_checked
def leaf0393 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 4), (facetIndex 6), (facetIndex 10), (facetIndex 23), (facetIndex 43), (facetIndex 59), (facetIndex 61), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 87), (facetIndex 99), (facetIndex 100)]
theorem leaf0393_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0393 = true := by
  decide +kernel
theorem leaf0393_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0393 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0393_counts_checked
def leaf0394 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 10), (facetIndex 12), (facetIndex 15), (facetIndex 22), (facetIndex 42), (facetIndex 45), (facetIndex 54), (facetIndex 58), (facetIndex 72), (facetIndex 84), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0394_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0394 = true := by
  decide +kernel
theorem leaf0394_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0394 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0394_counts_checked
def leaf0395 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 10), (facetIndex 11), (facetIndex 15), (facetIndex 21), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 59), (facetIndex 77), (facetIndex 87), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0395_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0395 = true := by
  decide +kernel
theorem leaf0395_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0395 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0395_counts_checked
def leaf0396 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 7), (facetIndex 10), (facetIndex 16), (facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 94), (facetIndex 97), (facetIndex 98)]
theorem leaf0396_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0396 = true := by
  decide +kernel
theorem leaf0396_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0396 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0396_counts_checked
def leaf0397 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 6), (facetIndex 10), (facetIndex 16), (facetIndex 21), (facetIndex 42), (facetIndex 45), (facetIndex 58), (facetIndex 72), (facetIndex 78), (facetIndex 86), (facetIndex 90), (facetIndex 97), (facetIndex 98)]
theorem leaf0397_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0397 = true := by
  decide +kernel
theorem leaf0397_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0397 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0397_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 199
 (.branch 99
 (.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (leaf0000))
 (.branch 2
 (.leaf (leaf0001))
 (.leaf (leaf0002))))
 (.branch 4
 (.leaf (leaf0003))
 (.branch 5
 (.leaf (leaf0004))
 (.leaf (leaf0005)))))
 (.branch 9
 (.branch 7
 (.leaf (leaf0006))
 (.branch 8
 (.leaf (leaf0007))
 (.leaf (leaf0008))))
 (.branch 10
 (.leaf (leaf0009))
 (.branch 11
 (.leaf (leaf0010))
 (.leaf (leaf0011))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (leaf0012))
 (.branch 14
 (.leaf (leaf0013))
 (.leaf (leaf0014))))
 (.branch 16
 (.leaf (leaf0015))
 (.branch 17
 (.leaf (leaf0016))
 (.leaf (leaf0017)))))
 (.branch 21
 (.branch 19
 (.leaf (leaf0018))
 (.branch 20
 (.leaf (leaf0019))
 (.leaf (leaf0020))))
 (.branch 22
 (.leaf (leaf0021))
 (.branch 23
 (.leaf (leaf0022))
 (.leaf (leaf0023)))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf (leaf0024))
 (.branch 26
 (.leaf (leaf0025))
 (.leaf (leaf0026))))
 (.branch 28
 (.leaf (leaf0027))
 (.branch 29
 (.leaf (leaf0028))
 (.leaf (leaf0029)))))
 (.branch 33
 (.branch 31
 (.leaf (leaf0030))
 (.branch 32
 (.leaf (leaf0031))
 (.leaf (leaf0032))))
 (.branch 34
 (.leaf (leaf0033))
 (.branch 35
 (.leaf (leaf0034))
 (.leaf (leaf0035))))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf (leaf0036))
 (.branch 38
 (.leaf (leaf0037))
 (.leaf (leaf0038))))
 (.branch 40
 (.leaf (leaf0039))
 (.branch 41
 (.leaf (leaf0040))
 (.leaf (leaf0041)))))
 (.branch 45
 (.branch 43
 (.leaf (leaf0042))
 (.branch 44
 (.leaf (leaf0043))
 (.leaf (leaf0044))))
 (.branch 47
 (.branch 46
 (.leaf (leaf0045))
 (.leaf (leaf0046)))
 (.branch 48
 (.leaf (leaf0047))
 (.leaf (leaf0048))))))))
 (.branch 74
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf (leaf0049))
 (.branch 51
 (.leaf (leaf0050))
 (.leaf (leaf0051))))
 (.branch 53
 (.leaf (leaf0052))
 (.branch 54
 (.leaf (leaf0053))
 (.leaf (leaf0054)))))
 (.branch 58
 (.branch 56
 (.leaf (leaf0055))
 (.branch 57
 (.leaf (leaf0056))
 (.leaf (leaf0057))))
 (.branch 59
 (.leaf (leaf0058))
 (.branch 60
 (.leaf (leaf0059))
 (.leaf (leaf0060))))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf (leaf0061))
 (.branch 63
 (.leaf (leaf0062))
 (.leaf (leaf0063))))
 (.branch 65
 (.leaf (leaf0064))
 (.branch 66
 (.leaf (leaf0065))
 (.leaf (leaf0066)))))
 (.branch 70
 (.branch 68
 (.leaf (leaf0067))
 (.branch 69
 (.leaf (leaf0068))
 (.leaf (leaf0069))))
 (.branch 72
 (.branch 71
 (.leaf (leaf0070))
 (.leaf (leaf0071)))
 (.branch 73
 (.leaf (leaf0072))
 (.leaf (leaf0073)))))))
 (.branch 86
 (.branch 80
 (.branch 77
 (.branch 75
 (.leaf (leaf0074))
 (.branch 76
 (.leaf (leaf0075))
 (.leaf (leaf0076))))
 (.branch 78
 (.leaf (leaf0077))
 (.branch 79
 (.leaf (leaf0078))
 (.leaf (leaf0079)))))
 (.branch 83
 (.branch 81
 (.leaf (leaf0080))
 (.branch 82
 (.leaf (leaf0081))
 (.leaf (leaf0082))))
 (.branch 84
 (.leaf (leaf0083))
 (.branch 85
 (.leaf (leaf0084))
 (.leaf (leaf0085))))))
 (.branch 92
 (.branch 89
 (.branch 87
 (.leaf (leaf0086))
 (.branch 88
 (.leaf (leaf0087))
 (.leaf (leaf0088))))
 (.branch 90
 (.leaf (leaf0089))
 (.branch 91
 (.leaf (leaf0090))
 (.leaf (leaf0091)))))
 (.branch 95
 (.branch 93
 (.leaf (leaf0092))
 (.branch 94
 (.leaf (leaf0093))
 (.leaf (leaf0094))))
 (.branch 97
 (.branch 96
 (.leaf (leaf0095))
 (.leaf (leaf0096)))
 (.branch 98
 (.leaf (leaf0097))
 (.leaf (leaf0098)))))))))
 (.branch 149
 (.branch 124
 (.branch 111
 (.branch 105
 (.branch 102
 (.branch 100
 (.leaf (leaf0099))
 (.branch 101
 (.leaf (leaf0100))
 (.leaf (leaf0101))))
 (.branch 103
 (.leaf (leaf0102))
 (.branch 104
 (.leaf (leaf0103))
 (.leaf (leaf0104)))))
 (.branch 108
 (.branch 106
 (.leaf (leaf0105))
 (.branch 107
 (.leaf (leaf0106))
 (.leaf (leaf0107))))
 (.branch 109
 (.leaf (leaf0108))
 (.branch 110
 (.leaf (leaf0109))
 (.leaf (leaf0110))))))
 (.branch 117
 (.branch 114
 (.branch 112
 (.leaf (leaf0111))
 (.branch 113
 (.leaf (leaf0112))
 (.leaf (leaf0113))))
 (.branch 115
 (.leaf (leaf0114))
 (.branch 116
 (.leaf (leaf0115))
 (.leaf (leaf0116)))))
 (.branch 120
 (.branch 118
 (.leaf (leaf0117))
 (.branch 119
 (.leaf (leaf0118))
 (.leaf (leaf0119))))
 (.branch 122
 (.branch 121
 (.leaf (leaf0120))
 (.leaf (leaf0121)))
 (.branch 123
 (.leaf (leaf0122))
 (.leaf (leaf0123)))))))
 (.branch 136
 (.branch 130
 (.branch 127
 (.branch 125
 (.leaf (leaf0124))
 (.branch 126
 (.leaf (leaf0125))
 (.leaf (leaf0126))))
 (.branch 128
 (.leaf (leaf0127))
 (.branch 129
 (.leaf (leaf0128))
 (.leaf (leaf0129)))))
 (.branch 133
 (.branch 131
 (.leaf (leaf0130))
 (.branch 132
 (.leaf (leaf0131))
 (.leaf (leaf0132))))
 (.branch 134
 (.leaf (leaf0133))
 (.branch 135
 (.leaf (leaf0134))
 (.leaf (leaf0135))))))
 (.branch 142
 (.branch 139
 (.branch 137
 (.leaf (leaf0136))
 (.branch 138
 (.leaf (leaf0137))
 (.leaf (leaf0138))))
 (.branch 140
 (.leaf (leaf0139))
 (.branch 141
 (.leaf (leaf0140))
 (.leaf (leaf0141)))))
 (.branch 145
 (.branch 143
 (.leaf (leaf0142))
 (.branch 144
 (.leaf (leaf0143))
 (.leaf (leaf0144))))
 (.branch 147
 (.branch 146
 (.leaf (leaf0145))
 (.leaf (leaf0146)))
 (.branch 148
 (.leaf (leaf0147))
 (.leaf (leaf0148))))))))
 (.branch 174
 (.branch 161
 (.branch 155
 (.branch 152
 (.branch 150
 (.leaf (leaf0149))
 (.branch 151
 (.leaf (leaf0150))
 (.leaf (leaf0151))))
 (.branch 153
 (.leaf (leaf0152))
 (.branch 154
 (.leaf (leaf0153))
 (.leaf (leaf0154)))))
 (.branch 158
 (.branch 156
 (.leaf (leaf0155))
 (.branch 157
 (.leaf (leaf0156))
 (.leaf (leaf0157))))
 (.branch 159
 (.leaf (leaf0158))
 (.branch 160
 (.leaf (leaf0159))
 (.leaf (leaf0160))))))
 (.branch 167
 (.branch 164
 (.branch 162
 (.leaf (leaf0161))
 (.branch 163
 (.leaf (leaf0162))
 (.leaf (leaf0163))))
 (.branch 165
 (.leaf (leaf0164))
 (.branch 166
 (.leaf (leaf0165))
 (.leaf (leaf0166)))))
 (.branch 170
 (.branch 168
 (.leaf (leaf0167))
 (.branch 169
 (.leaf (leaf0168))
 (.leaf (leaf0169))))
 (.branch 172
 (.branch 171
 (.leaf (leaf0170))
 (.leaf (leaf0171)))
 (.branch 173
 (.leaf (leaf0172))
 (.leaf (leaf0173)))))))
 (.branch 186
 (.branch 180
 (.branch 177
 (.branch 175
 (.leaf (leaf0174))
 (.branch 176
 (.leaf (leaf0175))
 (.leaf (leaf0176))))
 (.branch 178
 (.leaf (leaf0177))
 (.branch 179
 (.leaf (leaf0178))
 (.leaf (leaf0179)))))
 (.branch 183
 (.branch 181
 (.leaf (leaf0180))
 (.branch 182
 (.leaf (leaf0181))
 (.leaf (leaf0182))))
 (.branch 184
 (.leaf (leaf0183))
 (.branch 185
 (.leaf (leaf0184))
 (.leaf (leaf0185))))))
 (.branch 192
 (.branch 189
 (.branch 187
 (.leaf (leaf0186))
 (.branch 188
 (.leaf (leaf0187))
 (.leaf (leaf0188))))
 (.branch 190
 (.leaf (leaf0189))
 (.branch 191
 (.leaf (leaf0190))
 (.leaf (leaf0191)))))
 (.branch 195
 (.branch 193
 (.leaf (leaf0192))
 (.branch 194
 (.leaf (leaf0193))
 (.leaf (leaf0194))))
 (.branch 197
 (.branch 196
 (.leaf (leaf0195))
 (.leaf (leaf0196)))
 (.branch 198
 (.leaf (leaf0197))
 (.leaf (leaf0198))))))))))
 (.branch 298
 (.branch 248
 (.branch 223
 (.branch 211
 (.branch 205
 (.branch 202
 (.branch 200
 (.leaf (leaf0199))
 (.branch 201
 (.leaf (leaf0200))
 (.leaf (leaf0201))))
 (.branch 203
 (.leaf (leaf0202))
 (.branch 204
 (.leaf (leaf0203))
 (.leaf (leaf0204)))))
 (.branch 208
 (.branch 206
 (.leaf (leaf0205))
 (.branch 207
 (.leaf (leaf0206))
 (.leaf (leaf0207))))
 (.branch 209
 (.leaf (leaf0208))
 (.branch 210
 (.leaf (leaf0209))
 (.leaf (leaf0210))))))
 (.branch 217
 (.branch 214
 (.branch 212
 (.leaf (leaf0211))
 (.branch 213
 (.leaf (leaf0212))
 (.leaf (leaf0213))))
 (.branch 215
 (.leaf (leaf0214))
 (.branch 216
 (.leaf (leaf0215))
 (.leaf (leaf0216)))))
 (.branch 220
 (.branch 218
 (.leaf (leaf0217))
 (.branch 219
 (.leaf (leaf0218))
 (.leaf (leaf0219))))
 (.branch 221
 (.leaf (leaf0220))
 (.branch 222
 (.leaf (leaf0221))
 (.leaf (leaf0222)))))))
 (.branch 235
 (.branch 229
 (.branch 226
 (.branch 224
 (.leaf (leaf0223))
 (.branch 225
 (.leaf (leaf0224))
 (.leaf (leaf0225))))
 (.branch 227
 (.leaf (leaf0226))
 (.branch 228
 (.leaf (leaf0227))
 (.leaf (leaf0228)))))
 (.branch 232
 (.branch 230
 (.leaf (leaf0229))
 (.branch 231
 (.leaf (leaf0230))
 (.leaf (leaf0231))))
 (.branch 233
 (.leaf (leaf0232))
 (.branch 234
 (.leaf (leaf0233))
 (.leaf (leaf0234))))))
 (.branch 241
 (.branch 238
 (.branch 236
 (.leaf (leaf0235))
 (.branch 237
 (.leaf (leaf0236))
 (.leaf (leaf0237))))
 (.branch 239
 (.leaf (leaf0238))
 (.branch 240
 (.leaf (leaf0239))
 (.leaf (leaf0240)))))
 (.branch 244
 (.branch 242
 (.leaf (leaf0241))
 (.branch 243
 (.leaf (leaf0242))
 (.leaf (leaf0243))))
 (.branch 246
 (.branch 245
 (.leaf (leaf0244))
 (.leaf (leaf0245)))
 (.branch 247
 (.leaf (leaf0246))
 (.leaf (leaf0247))))))))
 (.branch 273
 (.branch 260
 (.branch 254
 (.branch 251
 (.branch 249
 (.leaf (leaf0248))
 (.branch 250
 (.leaf (leaf0249))
 (.leaf (leaf0250))))
 (.branch 252
 (.leaf (leaf0251))
 (.branch 253
 (.leaf (leaf0252))
 (.leaf (leaf0253)))))
 (.branch 257
 (.branch 255
 (.leaf (leaf0254))
 (.branch 256
 (.leaf (leaf0255))
 (.leaf (leaf0256))))
 (.branch 258
 (.leaf (leaf0257))
 (.branch 259
 (.leaf (leaf0258))
 (.leaf (leaf0259))))))
 (.branch 266
 (.branch 263
 (.branch 261
 (.leaf (leaf0260))
 (.branch 262
 (.leaf (leaf0261))
 (.leaf (leaf0262))))
 (.branch 264
 (.leaf (leaf0263))
 (.branch 265
 (.leaf (leaf0264))
 (.leaf (leaf0265)))))
 (.branch 269
 (.branch 267
 (.leaf (leaf0266))
 (.branch 268
 (.leaf (leaf0267))
 (.leaf (leaf0268))))
 (.branch 271
 (.branch 270
 (.leaf (leaf0269))
 (.leaf (leaf0270)))
 (.branch 272
 (.leaf (leaf0271))
 (.leaf (leaf0272)))))))
 (.branch 285
 (.branch 279
 (.branch 276
 (.branch 274
 (.leaf (leaf0273))
 (.branch 275
 (.leaf (leaf0274))
 (.leaf (leaf0275))))
 (.branch 277
 (.leaf (leaf0276))
 (.branch 278
 (.leaf (leaf0277))
 (.leaf (leaf0278)))))
 (.branch 282
 (.branch 280
 (.leaf (leaf0279))
 (.branch 281
 (.leaf (leaf0280))
 (.leaf (leaf0281))))
 (.branch 283
 (.leaf (leaf0282))
 (.branch 284
 (.leaf (leaf0283))
 (.leaf (leaf0284))))))
 (.branch 291
 (.branch 288
 (.branch 286
 (.leaf (leaf0285))
 (.branch 287
 (.leaf (leaf0286))
 (.leaf (leaf0287))))
 (.branch 289
 (.leaf (leaf0288))
 (.branch 290
 (.leaf (leaf0289))
 (.leaf (leaf0290)))))
 (.branch 294
 (.branch 292
 (.leaf (leaf0291))
 (.branch 293
 (.leaf (leaf0292))
 (.leaf (leaf0293))))
 (.branch 296
 (.branch 295
 (.leaf (leaf0294))
 (.leaf (leaf0295)))
 (.branch 297
 (.leaf (leaf0296))
 (.leaf (leaf0297)))))))))
 (.branch 348
 (.branch 323
 (.branch 310
 (.branch 304
 (.branch 301
 (.branch 299
 (.leaf (leaf0298))
 (.branch 300
 (.leaf (leaf0299))
 (.leaf (leaf0300))))
 (.branch 302
 (.leaf (leaf0301))
 (.branch 303
 (.leaf (leaf0302))
 (.leaf (leaf0303)))))
 (.branch 307
 (.branch 305
 (.leaf (leaf0304))
 (.branch 306
 (.leaf (leaf0305))
 (.leaf (leaf0306))))
 (.branch 308
 (.leaf (leaf0307))
 (.branch 309
 (.leaf (leaf0308))
 (.leaf (leaf0309))))))
 (.branch 316
 (.branch 313
 (.branch 311
 (.leaf (leaf0310))
 (.branch 312
 (.leaf (leaf0311))
 (.leaf (leaf0312))))
 (.branch 314
 (.leaf (leaf0313))
 (.branch 315
 (.leaf (leaf0314))
 (.leaf (leaf0315)))))
 (.branch 319
 (.branch 317
 (.leaf (leaf0316))
 (.branch 318
 (.leaf (leaf0317))
 (.leaf (leaf0318))))
 (.branch 321
 (.branch 320
 (.leaf (leaf0319))
 (.leaf (leaf0320)))
 (.branch 322
 (.leaf (leaf0321))
 (.leaf (leaf0322)))))))
 (.branch 335
 (.branch 329
 (.branch 326
 (.branch 324
 (.leaf (leaf0323))
 (.branch 325
 (.leaf (leaf0324))
 (.leaf (leaf0325))))
 (.branch 327
 (.leaf (leaf0326))
 (.branch 328
 (.leaf (leaf0327))
 (.leaf (leaf0328)))))
 (.branch 332
 (.branch 330
 (.leaf (leaf0329))
 (.branch 331
 (.leaf (leaf0330))
 (.leaf (leaf0331))))
 (.branch 333
 (.leaf (leaf0332))
 (.branch 334
 (.leaf (leaf0333))
 (.leaf (leaf0334))))))
 (.branch 341
 (.branch 338
 (.branch 336
 (.leaf (leaf0335))
 (.branch 337
 (.leaf (leaf0336))
 (.leaf (leaf0337))))
 (.branch 339
 (.leaf (leaf0338))
 (.branch 340
 (.leaf (leaf0339))
 (.leaf (leaf0340)))))
 (.branch 344
 (.branch 342
 (.leaf (leaf0341))
 (.branch 343
 (.leaf (leaf0342))
 (.leaf (leaf0343))))
 (.branch 346
 (.branch 345
 (.leaf (leaf0344))
 (.leaf (leaf0345)))
 (.branch 347
 (.leaf (leaf0346))
 (.leaf (leaf0347))))))))
 (.branch 373
 (.branch 360
 (.branch 354
 (.branch 351
 (.branch 349
 (.leaf (leaf0348))
 (.branch 350
 (.leaf (leaf0349))
 (.leaf (leaf0350))))
 (.branch 352
 (.leaf (leaf0351))
 (.branch 353
 (.leaf (leaf0352))
 (.leaf (leaf0353)))))
 (.branch 357
 (.branch 355
 (.leaf (leaf0354))
 (.branch 356
 (.leaf (leaf0355))
 (.leaf (leaf0356))))
 (.branch 358
 (.leaf (leaf0357))
 (.branch 359
 (.leaf (leaf0358))
 (.leaf (leaf0359))))))
 (.branch 366
 (.branch 363
 (.branch 361
 (.leaf (leaf0360))
 (.branch 362
 (.leaf (leaf0361))
 (.leaf (leaf0362))))
 (.branch 364
 (.leaf (leaf0363))
 (.branch 365
 (.leaf (leaf0364))
 (.leaf (leaf0365)))))
 (.branch 369
 (.branch 367
 (.leaf (leaf0366))
 (.branch 368
 (.leaf (leaf0367))
 (.leaf (leaf0368))))
 (.branch 371
 (.branch 370
 (.leaf (leaf0369))
 (.leaf (leaf0370)))
 (.branch 372
 (.leaf (leaf0371))
 (.leaf (leaf0372)))))))
 (.branch 385
 (.branch 379
 (.branch 376
 (.branch 374
 (.leaf (leaf0373))
 (.branch 375
 (.leaf (leaf0374))
 (.leaf (leaf0375))))
 (.branch 377
 (.leaf (leaf0376))
 (.branch 378
 (.leaf (leaf0377))
 (.leaf (leaf0378)))))
 (.branch 382
 (.branch 380
 (.leaf (leaf0379))
 (.branch 381
 (.leaf (leaf0380))
 (.leaf (leaf0381))))
 (.branch 383
 (.leaf (leaf0382))
 (.branch 384
 (.leaf (leaf0383))
 (.leaf (leaf0384))))))
 (.branch 391
 (.branch 388
 (.branch 386
 (.leaf (leaf0385))
 (.branch 387
 (.leaf (leaf0386))
 (.leaf (leaf0387))))
 (.branch 389
 (.leaf (leaf0388))
 (.branch 390
 (.leaf (leaf0389))
 (.leaf (leaf0390)))))
 (.branch 394
 (.branch 392
 (.leaf (leaf0391))
 (.branch 393
 (.leaf (leaf0392))
 (.leaf (leaf0393))))
 (.branch 396
 (.branch 395
 (.leaf (leaf0394))
 (.leaf (leaf0395)))
 (.branch 397
 (.leaf (leaf0396))
 (.leaf (leaf0397)))))))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":1},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":3},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":20},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":6,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":6,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0042\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0042\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0068\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0066\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0062\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0062\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0074\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0071\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0071\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0079\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0079\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0077\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0077\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record007" 233

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record007" "{\"ridges\":[[0,13],[1,7],[1,21],[2,35],[2,41],[3,259],[4,290],[5,13],[5,73],[5,76],[7,97],[8,81],[8,273],[8,321],[8,336],[9,289],[9,321],[9,352],[10,134],[10,140],[11,134],[11,146],[12,168],[13,274],[13,386],[13,400],[14,290],[14,416],[15,76],[15,580],[16,524],[17,84],[17,532],[17,580],[17,592],[18,644],[18,656],[19,552],[19,584],[19,608],[20,168],[20,648],[20,672],[21,11],[21,13],[21,14],[21,19],[21,21],[21,22],[22,7],[22,13],[22,14],[22,35],[22,41],[22,42],[23,7],[23,11],[23,14],[23,69],[23,73],[23,76],[24,7],[24,11],[24,13],[24,134],[24,138],[24,140],[25,7],[25,19],[25,69],[25,81],[26,7],[26,19],[26,21],[26,134],[26,146],[26,148],[27,7],[27,21],[27,22],[27,259],[27,273],[27,274],[28,102],[29,165],[30,326],[31,389],[32,90],[33,153],[34,11],[34,35],[34,42],[34,73],[34,97],[34,104],[35,11],[35,35],[35,138],[35,162],[35,168],[36,11],[36,41],[36,42],[36,259],[36,289],[36,290],[37,330],[38,393],[39,114],[40,177],[41,19],[41,35],[41,273],[41,274],[41,289],[41,290],[42,19],[42,81],[42,259],[42,274],[42,321],[42,336],[43,19],[43,146],[43,259],[43,386],[43,400],[44,35],[44,97],[44,259],[44,290],[44,321],[44,352],[45,35],[45,162],[45,259],[45,289],[45,386],[45,416],[46,13],[46,21],[46,76],[46,81],[46,84],[47,153],[48,537],[49,13],[49,41],[49,76],[49,97],[49,104],[50,165],[51,549],[52,13],[52,69],[52,73],[52,524],[52,580],[52,584],[53,21],[53,69],[53,84],[53,273],[53,321],[53,336],[54,21],[54,69],[54,81],[54,532],[54,580],[54,592],[55,389],[56,549],[57,537],[58,41],[58,73],[58,104],[58,289],[58,321],[58,352],[59,41],[59,73],[59,97],[59,552],[59,584],[59,608],[60,393],[61,81],[61,97],[61,273],[61,289],[61,336],[61,352],[62,561],[63,177],[64,90],[65,14],[65,140],[65,146],[65,148],[66,538],[67,102],[68,14],[68,42],[68,134],[68,140],[68,162],[68,168],[69,550],[70,134],[70,138],[70,524],[70,644],[70,648],[71,326],[72,22],[72,134],[72,148],[72,274],[72,386],[72,400],[73,22],[73,134],[73,146],[73,532],[73,644],[73,656],[74,550],[75,538],[76,330],[77,42],[77,138],[77,168],[77,290],[77,386],[77,416],[78,42],[78,138],[78,162],[78,552],[78,648],[78,672],[79,114],[80,146],[80,162],[80,274],[80,290],[80,400],[80,416],[81,562],[82,216],[83,76],[83,84],[83,524],[83,532],[83,584],[83,592],[84,140],[84,148],[84,524],[84,532],[84,648],[84,656],[85,228],[86,76],[86,104],[86,524],[86,552],[86,608],[87,140],[87,168],[87,524],[87,552],[87,644],[87,672],[88,140],[88,580],[88,584],[88,644],[88,648],[89,452],[90,148],[90,580],[90,592],[90,644],[90,656],[91,228],[92,216],[93,456],[94,104],[94,168],[94,584],[94,608],[94,648],[94,672],[95,336],[95,400],[95,416],[96,592],[96,608],[96,656],[96,672],[97,336],[97,352],[97,608],[97,816],[98,400],[98,416],[98,656],[98,672],[98,816],[99,336],[99,400],[99,592],[99,656],[99,960],[100,352],[100,416],[100,608],[100,672],[100,960]],\"owners\":[[1,7,[0,22,23,24,28,29,30,31],[25,26,27]],[22,7,[1,25,26,27,30,31],[0,23,24,28,29]],[23,7,[1,26,27,29,31],[0,22,24,25,28,30]],[24,7,[1,25,27,28,30],[0,22,23,26,29,31]],[25,7,[0,22,24,29,31],[1,23,26,27,28,30]],[26,7,[0,22,23,28,30],[1,24,25,27,29,31]],[27,7,[0,22,23,24,28,29],[1,25,26,30,31]],[21,11,[2,34,35,36,37,38],[0,23,24,32,33]],[23,11,[2,33,35,36,38],[0,21,24,32,34,37]],[24,11,[2,32,34,36,37],[0,21,23,33,35,38]],[34,11,[0,21,24,33,38],[2,23,32,35,36,37]],[35,11,[0,21,23,32,37],[2,24,33,34,36,38]],[36,11,[0,21,23,24,32,33],[2,34,35,37,38]],[0,13,[5,46,47,48,49,50,51,52],[21,22,24]],[5,13,[0,21,22,24,47,48,50,51],[46,49,52]],[21,13,[5,49,50,51,52],[0,22,24,46,47,48]],[22,13,[5,46,47,48,52],[0,21,24,49,50,51]],[24,13,[5,46,48,49,51,52],[0,21,22,47,50]],[46,13,[0,22,24,50,51],[5,21,47,48,49,52]],[49,13,[0,21,24,47,48],[5,22,46,50,51,52]],[52,13,[0,21,22,24,47,50],[5,46,48,49,51]],[21,14,[10,67,68,69,70],[0,22,23,64,65,66]],[22,14,[10,64,65,66,70],[0,21,23,67,68,69]],[23,14,[10,65,66,68,69,70],[0,21,22,64,67]],[65,14,[0,22,23,67,69],[10,21,64,66,68,70]],[68,14,[0,21,23,64,66],[10,22,65,67,69,70]],[21,19,[3,39,40,41,42,43],[1,25,26,32,33]],[25,19,[3,33,40,41,43],[1,21,26,32,39,42]],[26,19,[3,32,39,41,42],[1,21,25,33,40,43]],[41,19,[1,21,25,26,32,33],[3,39,40,42,43]],[42,19,[1,21,26,33,40],[3,25,32,39,41,43]],[43,19,[1,21,25,32,39],[3,26,33,40,41,42]],[1,21,[6,46,47,48,53,54,55],[21,26,27]],[21,21,[6,53,54,55],[1,26,27,46,47,48]],[26,21,[6,46,48,53,54],[1,21,27,47,55]],[27,21,[6,46,47,48,54],[1,21,26,53,55]],[46,21,[1,26,27,55],[6,21,47,48,53,54]],[53,21,[1,21,26,47,48],[6,27,46,54,55]],[54,21,[1,21,26,27,47,55],[6,46,48,53]],[21,22,[11,71,72,73],[1,25,27,64,65,66]],[27,22,[11,64,65,66,73],[1,21,25,71,72]],[72,22,[1,21,25,64,66],[11,27,65,71,73]],[73,22,[1,21,25,27,64,71],[11,65,66,72]],[2,35,[4,28,29,39,40,41,44,45],[22,34,35]],[22,35,[4,39,40,41,44,45],[2,28,29,34,35]],[34,35,[4,29,40,41,45],[2,22,28,35,39,44]],[35,35,[4,28,39,41,44],[2,22,29,34,40,45]],[41,35,[2,22,28,29,34,35],[4,39,40,44,45]],[44,35,[2,22,29,35,40],[4,28,34,39,41,45]],[45,35,[2,22,28,34,39],[4,29,35,40,41,44]],[2,41,[7,49,50,51,58,59,60],[22,35,36]],[22,41,[7,58,59,60],[2,35,36,49,50,51]],[36,41,[7,49,50,51,59],[2,22,35,58,60]],[49,41,[2,35,36,60],[7,22,50,51,58,59]],[58,41,[2,22,35,50,51],[7,36,49,59,60]],[59,41,[2,22,35,36,50,60],[7,49,51,58]],[22,42,[12,76,77,78],[2,34,36,67,68,69]],[34,42,[12,68,69,77,78],[2,22,36,67,76]],[36,42,[12,67,68,69,78],[2,22,34,76,77]],[68,42,[2,34,36,76],[12,22,67,69,77,78]],[77,42,[2,22,34,67,69],[12,36,68,76,78]],[78,42,[2,22,34,36,67,76],[12,68,69,77]],[3,259,[4,30,31,36,37,38,44,45],[27,42,43]],[27,259,[4,36,37,38,44,45],[3,30,31,42,43]],[36,259,[3,27,30,31,42,43],[4,37,38,44,45]],[42,259,[4,31,36,38,45],[3,27,30,37,43,44]],[43,259,[4,30,36,37,44],[3,27,31,38,42,45]],[44,259,[3,27,31,38,43],[4,30,36,37,42,45]],[45,259,[3,27,30,37,42],[4,31,36,38,43,44]],[8,273,[3,27,41,43,55,63],[53,61]],[27,273,[8,61,63],[3,41,43,53,55]],[41,273,[8,53,55],[3,27,43,61,63]],[53,273,[3,41,43,63],[8,27,55,61]],[61,273,[3,27,43,55],[8,41,53,63]],[13,274,[3,27,41,42,71,79],[72,80]],[27,274,[13,79,80],[3,41,42,71,72]],[41,274,[13,71,72],[3,27,42,79,80]],[42,274,[13,72,80],[3,27,41,71,79]],[72,274,[3,41,42,79],[13,27,71,80]],[80,274,[3,27,42,71],[13,41,72,79]],[9,289,[4,36,41,45,60,63],[58,61]],[36,289,[9,61,63],[4,41,45,58,60]],[41,289,[9,58,60],[4,36,45,61,63]],[45,289,[9,58,61],[4,36,41,60,63]],[58,289,[4,41,45,63],[9,36,60,61]],[61,289,[4,36,45,60],[9,41,58,63]],[4,290,[14,76,77,79,80],[36,41,44]],[14,290,[4,36,41,44,76,79],[77,80]],[36,290,[14,79,80],[4,41,44,76,77]],[41,290,[14,76,77],[4,36,44,79,80]],[44,290,[14,77,80],[4,36,41,76,79]],[77,290,[4,41,44,79],[14,36,76,80]],[80,290,[4,36,44,76],[14,41,77,79]],[23,69,[6,53,54,56],[5,25,28,30,49,52]],[25,69,[5,49,52,56],[6,23,28,30,53,54]],[52,69,[6,25,28,30,53],[5,23,49,54,56]],[53,69,[5,23,28,49,52,56],[6,25,30,54]],[54,69,[5,23,28,30,49],[6,25,52,53,56]],[5,73,[7,32,34,37,57,58,59],[23,46,52]],[23,73,[7,57,58,59],[5,32,34,37,46,52]],[34,73,[5,46,52,57],[7,23,32,37,58,59]],[52,73,[7,32,34,37,58],[5,23,46,57,59]],[58,73,[5,23,32,46,52,57],[7,34,37,59]],[59,73,[5,23,32,37,46],[7,34,52,57,58]],[5,76,[15,64,67,82,83,85,86,88],[23,46,49]],[15,76,[5,23,46,49,64,67,82,85],[83,86,88]],[23,76,[15,82,83,85,86,88],[5,46,49,64,67]],[46,76,[15,67,85,86,88],[5,23,49,64,82,83]],[49,76,[15,64,82,83,88],[5,23,46,67,85,86]],[83,76,[5,23,49,67,85],[15,46,64,82,86,88]],[86,76,[5,23,46,64,82],[15,49,67,83,85,88]],[8,81,[6,25,32,39,46,54,57,62],[42,61]],[25,81,[8,57,61,62],[6,32,39,42,46,54]],[42,81,[6,46,54,57,62],[8,25,32,39,61]],[46,81,[8,39,42,61,62],[6,25,32,54,57]],[54,81,[8,32,39,42,61],[6,25,46,57,62]],[61,81,[6,25,32,46,54,57],[8,39,42,62]],[17,84,[6,25,46,53,64,71,82,89],[83,90]],[46,84,[17,71,89,90],[6,25,53,64,82,83]],[53,84,[17,64,82,83,90],[6,25,46,71,89]],[83,84,[6,25,53,71,89],[17,46,64,82,90]],[7,97,[9,28,39,44,56,61,62],[34,49,59]],[34,97,[9,56,61,62],[7,28,39,44,49,59]],[44,97,[7,49,56,59,62],[9,28,34,39,61]],[49,97,[9,39,44,61,62],[7,28,34,56,59]],[59,97,[9,28,39,44,61],[7,34,49,56,62]],[61,97,[7,28,34,49,56,59],[9,39,44,62]],[34,104,[19,85,86,93,94],[7,49,58,67,76]],[49,104,[19,76,93,94],[7,34,58,67,85,86]],[58,104,[19,67,85,86,94],[7,34,49,76,93]],[86,104,[7,34,58,76,93],[19,49,67,85,94]],[94,104,[7,34,49,58,67,76],[19,85,86,93]],[8,321,[9,30,37,44,58],[42,53]],[9,321,[8,30,37,42,53],[44,58]],[42,321,[9,58],[8,30,37,44,53]],[44,321,[8,53],[9,30,37,42,58]],[53,321,[9,37,44,58],[8,30,42]],[58,321,[8,30,42,53],[9,37,44]],[8,336,[71,79,89,95,97,99],[42,53,61]],[42,336,[89,95,97,99],[8,53,61,71,79]],[53,336,[79,95,97,99],[8,42,61,71,89]],[61,336,[71,89,99],[8,42,53,79,95,97]],[95,336,[8,42,53,71],[61,79,89,97,99]],[97,336,[8,42,53,71,89],[61,79,95,99]],[99,336,[8,42,53,61,71,79],[89,95,97]],[9,352,[76,79,93,95,97,100],[44,58,61]],[44,352,[93,95,97,100],[9,58,61,76,79]],[58,352,[79,95,97,100],[9,44,61,76,93]],[61,352,[76,93,100],[9,44,58,79,95,97]],[97,352,[9,44,58,76,93],[61,79,95,100]],[100,352,[9,44,58,61,76,79],[93,95,97]],[10,134,[11,26,29,31,72,73,74],[24,68,70]],[11,134,[10,24,29,31,68,70,74],[26,72,73]],[24,134,[11,72,73,74],[10,26,29,31,68,70]],[26,134,[10,68,70,74],[11,24,29,31,72,73]],[68,134,[11,26,31,72,73],[10,24,29,70,74]],[70,134,[11,26,29,31,72],[10,24,68,73,74]],[72,134,[10,24,29,68,70,74],[11,26,31,73]],[73,134,[10,24,29,31,68],[11,26,70,72,74]],[24,138,[12,75,77,78],[10,33,35,38,65,70]],[35,138,[10,65,70,75],[12,24,33,38,77,78]],[70,138,[12,33,35,38,77],[10,24,65,75,78]],[77,138,[10,24,33,65,70,75],[12,35,38,78]],[78,138,[10,24,33,38,65],[12,35,70,75,77]],[10,140,[16,47,50,82,84,85,87,88],[24,65,68]],[24,140,[16,82,84,85,87,88],[10,47,50,65,68]],[65,140,[16,50,85,87,88],[10,24,47,68,82,84]],[68,140,[16,47,82,84,88],[10,24,50,65,85,87]],[84,140,[10,24,50,68,85],[16,47,65,82,87,88]],[87,140,[10,24,47,65,82],[16,50,68,84,85,88]],[88,140,[10,24,47,50,65,68],[16,82,84,85,87]],[11,146,[13,33,40,43,75,80,81],[26,65,73]],[26,146,[13,75,80,81],[11,33,40,43,65,73]],[43,146,[11,65,73,75,81],[13,26,33,40,80]],[65,146,[13,40,43,80,81],[11,26,33,73,75]],[73,146,[13,33,40,43,80],[11,26,65,75,81]],[80,146,[11,26,33,65,73,75],[13,40,43,81]],[26,148,[18,82,84,89,90],[11,47,55,65,72]],[65,148,[18,55,89,90],[11,26,47,72,82,84]],[72,148,[18,47,82,84,90],[11,26,55,65,89]],[84,148,[11,26,55,72,89],[18,47,65,82,90]],[90,148,[11,26,47,55,65,72],[18,82,84,89]],[35,162,[14,74,80,81],[12,29,40,45,68,78]],[45,162,[12,68,74,78,81],[14,29,35,40,80]],[68,162,[14,40,45,80,81],[12,29,35,74,78]],[78,162,[14,29,40,45,80],[12,35,68,74,81]],[80,162,[12,29,35,68,74,78],[14,40,45,81]],[12,168,[20,50,60,85,87,93,94],[35,68,77]],[20,168,[12,35,50,60,68,77,85,93],[87,94]],[35,168,[20,85,87,93,94],[12,50,60,68,77]],[68,168,[20,60,93,94],[12,35,50,77,85,87]],[77,168,[20,50,85,87,94],[12,35,60,68,93]],[87,168,[12,35,60,77,93],[20,50,68,85,94]],[94,168,[12,35,50,60,68,77],[20,85,87,93]],[13,386,[14,31,38,45,77],[43,72]],[43,386,[14,77],[13,31,38,45,72]],[45,386,[13,72],[14,31,38,43,77]],[72,386,[14,38,45,77],[13,31,43]],[77,386,[13,31,43,72],[14,38,45]],[13,400,[55,63,89,95,98,99],[43,72,80]],[43,400,[89,95,98,99],[13,55,63,72,80]],[72,400,[63,95,98,99],[13,43,55,80,89]],[80,400,[55,89,99],[13,43,63,72,95,98]],[95,400,[13,43,55,72],[63,80,89,98,99]],[98,400,[13,43,55,72,89],[63,80,95,99]],[99,400,[13,43,55,63,72,80],[89,95,98]],[14,416,[60,63,93,95,98,100],[45,77,80]],[45,416,[93,95,98,100],[14,60,63,77,80]],[77,416,[63,95,98,100],[14,45,60,80,93]],[80,416,[60,93,100],[14,45,63,77,95,98]],[95,416,[14,45,60,77],[63,80,93,98,100]],[98,416,[14,45,60,77,93],[63,80,95,100]],[100,416,[14,45,60,63,77,80],[93,95,98]],[16,524,[15,48,51,52,66,69,83,86],[70,84,87]],[52,524,[16,66,69,70,84,87],[15,48,51,83,86]],[70,524,[15,48,51,52,83,86],[16,66,69,84,87]],[83,524,[16,51,69,70,87],[15,48,52,66,84,86]],[84,524,[15,51,52,69,86],[16,48,66,70,83,87]],[86,524,[16,48,66,70,84],[15,51,52,69,83,87]],[87,524,[15,48,52,66,83],[16,51,69,70,84,86]],[15,580,[17,54,56,90,91],[52,86,88]],[17,580,[15,52,56,86,88,91],[54,90]],[52,580,[17,90,91],[15,54,56,86,88]],[54,580,[15,86,88,91],[17,52,56,90]],[88,580,[17,54,56],[15,52,86,90,91]],[90,580,[15,52,56,86],[17,54,88,91]],[19,584,[15,52,57,83,88,92],[59,94]],[52,584,[19,92,94],[15,57,59,83,88]],[59,584,[15,83,88,92],[19,52,57,94]],[83,584,[19,59,94],[15,52,57,88,92]],[88,584,[19,57,59],[15,52,83,92,94]],[94,584,[15,52,57,83],[19,59,88,92]],[18,644,[16,70,74,87,88,91],[73,90]],[70,644,[18,90,91],[16,73,74,87,88]],[73,644,[16,87,88,91],[18,70,74,90]],[87,644,[18,73,90],[16,70,74,88,91]],[88,644,[18,73,74],[16,70,87,90,91]],[90,644,[16,70,74,87],[18,73,88,91]],[20,648,[16,70,75,84,88,92],[78,94]],[70,648,[20,92,94],[16,75,78,84,88]],[78,648,[16,84,88,92],[20,70,75,94]],[84,648,[20,78,94],[16,70,75,88,92]],[88,648,[20,75,78],[16,70,84,92,94]],[94,648,[16,70,75,84],[20,78,88,92]],[17,532,[18,48,66,73,84],[54,83]],[54,532,[18,66,73,84],[17,48,83]],[73,532,[17,48,54,83],[18,66,84]],[83,532,[18,73],[17,48,54,66,84]],[84,532,[17,54],[18,48,66,73,83]],[17,592,[57,62,92,96,97,99],[54,83,90]],[54,592,[92,96,97,99],[17,57,62,83,90]],[83,592,[62,96,97,99],[17,54,57,90,92]],[90,592,[57,62,97],[17,54,83,92,96,99]],[96,592,[17,54,57,83],[62,90,92,97,99]],[99,592,[17,54,57,62,83],[90,92,96,97]],[18,656,[75,81,92,96,98,99],[73,84,90]],[73,656,[92,96,98,99],[18,75,81,84,90]],[84,656,[81,96,98,99],[18,73,75,90,92]],[90,656,[75,81,98],[18,73,84,92,96,99]],[96,656,[18,73,75,84],[81,90,92,98,99]],[98,656,[18,73,75,84,90,92],[81,96,99]],[99,656,[18,73,75,81,84],[90,92,96,98]],[19,552,[20,51,69,78,87],[59,86]],[59,552,[20,69,78,87],[19,51,86]],[78,552,[19,51,59,86],[20,69,87]],[86,552,[20,78],[19,51,59,69,87]],[87,552,[19,59],[20,51,69,78,86]],[19,608,[56,62,91,96,97,100],[59,86,94]],[59,608,[91,96,97,100],[19,56,62,86,94]],[86,608,[62,96,97,100],[19,56,59,91,94]],[94,608,[56,62,97],[19,59,86,91,96,100]],[96,608,[19,56,59,86],[62,91,94,97,100]],[97,608,[19,56,59,86,91,94],[62,96,100]],[100,608,[19,56,59,62,86],[91,94,96,97]],[20,672,[74,81,91,96,98,100],[78,87,94]],[78,672,[91,96,98,100],[20,74,81,87,94]],[87,672,[81,96,98,100],[20,74,78,91,94]],[94,672,[74,81,98],[20,78,87,91,96,100]],[96,672,[20,74,78,87],[81,91,94,98,100]],[98,672,[20,74,78,87,91,94],[81,96,100]],[100,672,[20,74,78,81,87],[91,94,96,98]],[28,102,[67],[]],[67,102,[28],[]],[29,165,[50],[]],[50,165,[29],[]],[30,326,[71],[]],[71,326,[30],[]],[31,389,[55],[]],[55,389,[31],[]],[32,90,[64],[]],[64,90,[32],[]],[33,153,[47],[]],[47,153,[33],[]],[37,330,[76],[]],[76,330,[37],[]],[38,393,[60],[]],[60,393,[38],[]],[39,114,[79],[]],[79,114,[39],[]],[40,177,[63],[]],[63,177,[40],[]],[48,537,[57],[]],[57,537,[48],[]],[51,549,[56],[]],[56,549,[51],[]],[62,561,[],[]],[66,538,[75],[]],[75,538,[66],[]],[69,550,[74],[]],[74,550,[69],[]],[81,562,[],[]],[82,216,[92],[]],[92,216,[82],[]],[85,228,[91],[]],[91,228,[85],[]],[89,452,[],[]],[93,456,[],[]],[97,816,[98],[]],[98,816,[97],[]],[99,960,[100],[]],[100,960,[99],[]]],\"edges\":[[34,[17,18,48,54,57,62,66,73,75,81,83,84,90,92,96,97,98,99]],[38,[19,20,51,56,59,62,69,74,78,81,86,87,91,94,96,97,98,100]],[40,[8,9,30,37,42,44,53,58,61,71,76,79,89,93,95,97,99,100]]],\"groupings\":[1,2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-22],[-24,-22],[-24,-23],[-25,-11],[-25,-22],[-25,-23],[-25,-24],[-26,-2],[-26,-22],[-27,-22],[-27,-25],[-27,-26],[-28,-2],[-28,-22],[-28,-26],[-28,-27],[-35,-3],[-35,-23],[-35,-24],[-35,-26],[-36,-3],[-36,-23],[-36,-25],[-36,-27],[-36,-35],[-37,-3],[-37,-5],[-37,-23],[-37,-35],[-37,-36],[-42,-28],[-42,-37],[-43,-9],[-43,-24],[-43,-26],[-43,-28],[-43,-35],[-43,-42],[-44,-25],[-44,-27],[-44,-28],[-44,-36],[-44,-42],[-44,-43],[-45,-10],[-45,-24],[-45,-26],[-45,-35],[-45,-37],[-45,-42],[-45,-43],[-46,-5],[-46,-25],[-46,-27],[-46,-36],[-46,-37],[-46,-42],[-46,-44],[-46,-45],[-47,-6],[-47,-22],[-47,-24],[-47,-26],[-50,-23],[-50,-24],[-50,-35],[-50,-47],[-53,-16],[-53,-24],[-53,-47],[-53,-50],[-54,-9],[-54,-26],[-54,-28],[-54,-43],[-54,-47],[-55,-26],[-55,-47],[-55,-53],[-55,-54],[-57,-23],[-57,-50],[-57,-53],[-57,-55],[-59,-8],[-59,-10],[-59,-35],[-59,-37],[-59,-45],[-59,-50],[-60,-35],[-60,-50],[-60,-53],[-60,-55],[-60,-57],[-60,-59],[-62,-42],[-62,-43],[-62,-45],[-62,-54],[-62,-59],[-66,-11],[-66,-22],[-66,-25],[-66,-27],[-66,-47],[-69,-23],[-69,-25],[-69,-36],[-69,-50],[-69,-57],[-69,-66],[-71,-11],[-71,-25],[-71,-66],[-71,-69],[-73,-27],[-73,-28],[-73,-44],[-73,-54],[-73,-66],[-74,-27],[-74,-66],[-74,-71],[-74,-73],[-78,-36],[-78,-37],[-78,-46],[-78,-59],[-78,-69],[-79,-13],[-79,-36],[-79,-69],[-79,-71],[-79,-74],[-79,-78],[-81,-42],[-81,-44],[-81,-46],[-81,-62],[-81,-73],[-81,-78],[-84,-16],[-84,-22],[-84,-47],[-84,-53],[-84,-55],[-84,-66],[-85,-19],[-85,-22],[-85,-47],[-85,-66],[-85,-71],[-85,-74],[-85,-84],[-87,-23],[-87,-50],[-87,-53],[-87,-57],[-87,-60],[-87,-69],[-87,-84],[-88,-23],[-88,-50],[-88,-57],[-88,-69],[-88,-71],[-88,-79],[-88,-85],[-88,-87],[-89,-16],[-89,-52],[-89,-53],[-89,-71],[-89,-84],[-89,-85],[-89,-87],[-89,-88],[-91,-18],[-91,-55],[-91,-74],[-91,-84],[-91,-85],[-95,-20],[-95,-52],[-95,-60],[-95,-79],[-95,-87],[-95,-88],[-95,-89],[-95,-91],[-96,-42],[-96,-89],[-97,-42],[-97,-89],[-98,-42],[-98,-62],[-98,-81],[-99,-42],[-99,-62],[-99,-81],[-100,-89],[-100,-91],[-100,-95],[-101,-89],[-2,1,23,24,25,29,30,31,32],[-23,2,26,27,28,31,32],[-24,2,27,28,30,32],[-25,2,26,28,29,31],[-26,1,23,25,30,32],[-27,1,23,24,29,31],[-28,1,23,24,25,29,30],[-22,3,35,36,37,38,39],[-24,3,34,36,37,39],[-25,3,33,35,37,38],[-35,1,22,25,34,39],[-36,1,22,24,33,38],[-37,1,22,24,25,33,34],[-1,6,47,48,49,50,51,52,53],[-6,1,22,23,25,48,49,51,52],[-22,6,50,51,52,53],[-23,6,47,48,49,53],[-25,6,47,49,50,52,53],[-47,1,23,25,51,52],[-50,1,22,25,48,49],[-53,1,22,23,25,48,51],[-22,11,68,69,70,71],[-23,11,65,66,67,71],[-24,11,66,67,69,70,71],[-66,1,23,24,68,70],[-69,1,22,24,65,67],[-22,4,40,41,42,43,44],[-26,4,34,41,42,44],[-27,4,33,40,42,43],[-42,2,22,26,27,33,34],[-43,2,22,27,34,41],[-44,2,22,26,33,40],[-2,7,47,48,49,54,55,56],[-22,7,54,55,56],[-27,7,47,49,54,55],[-28,7,47,48,49,55],[-47,2,27,28,56],[-54,2,22,27,48,49],[-55,2,22,27,28,48,56],[-22,12,72,73,74],[-28,12,65,66,67,74],[-73,2,22,26,65,67],[-74,2,22,26,28,65,72],[-3,5,29,30,40,41,42,45,46],[-23,5,40,41,42,45,46],[-35,5,30,41,42,46],[-36,5,29,40,42,45],[-42,3,23,29,30,35,36],[-45,3,23,30,36,41],[-46,3,23,29,35,40],[-3,8,50,51,52,59,60,61],[-23,8,59,60,61],[-37,8,50,51,52,60],[-50,3,36,37,61],[-59,3,23,36,51,52],[-60,3,23,36,37,51,61],[-23,13,77,78,79],[-35,13,69,70,78,79],[-37,13,68,69,70,79],[-69,3,35,37,77],[-78,3,23,35,68,70],[-79,3,23,35,37,68,77],[-4,5,31,32,37,38,39,45,46],[-28,5,37,38,39,45,46],[-37,4,28,31,32,43,44],[-43,5,32,37,39,46],[-44,5,31,37,38,45],[-45,4,28,32,39,44],[-46,4,28,31,38,43],[-9,4,28,42,44,56,64],[-28,9,62,64],[-42,9,54,56],[-54,4,42,44,64],[-62,4,28,44,56],[-14,4,28,42,43,72,80],[-28,14,80,81],[-42,14,72,73],[-43,14,73,81],[-73,4,42,43,80],[-81,4,28,43,72],[-10,5,37,42,46,61,64],[-37,10,62,64],[-42,10,59,61],[-46,10,59,62],[-59,5,42,46,64],[-62,5,37,46,61],[-5,15,77,78,80,81],[-15,5,37,42,45,77,80],[-37,15,80,81],[-42,15,77,78],[-45,15,78,81],[-78,5,42,45,80],[-81,5,37,45,77],[-24,7,54,55,57],[-26,6,50,53,57],[-53,7,26,29,31,54],[-54,6,24,29,50,53,57],[-55,6,24,29,31,50],[-6,8,33,35,38,58,59,60],[-24,8,58,59,60],[-35,6,47,53,58],[-53,8,33,35,38,59],[-59,6,24,33,47,53,58],[-60,6,24,33,38,47],[-6,16,65,68,83,84,86,87,89],[-16,6,24,47,50,65,68,83,86],[-24,16,83,84,86,87,89],[-47,16,68,86,87,89],[-50,16,65,83,84,89],[-84,6,24,50,68,86],[-87,6,24,47,65,83],[-9,7,26,33,40,47,55,58,63],[-26,9,58,62,63],[-43,7,47,55,58,63],[-47,9,40,43,62,63],[-55,9,33,40,43,62],[-62,7,26,33,47,55,58],[-18,7,26,47,54,65,72,83,90],[-47,18,72,90,91],[-54,18,65,83,84,91],[-84,7,26,54,72,90],[-8,10,29,40,45,57,62,63],[-35,10,57,62,63],[-45,8,50,57,60,63],[-50,10,40,45,62,63],[-60,10,29,40,45,62],[-62,8,29,35,50,57,60],[-35,20,86,87,94,95],[-50,20,77,94,95],[-59,20,68,86,87,95],[-87,8,35,59,77,94],[-95,8,35,50,59,68,77],[-9,10,31,38,45,59],[-10,9,31,38,43,54],[-43,10,59],[-45,9,54],[-54,10,38,45,59],[-59,9,31,43,54],[-9,72,80,90,96,98,100],[-43,90,96,98,100],[-54,80,96,98,100],[-62,72,90,100],[-96,9,43,54,72],[-98,9,43,54,72,90],[-100,9,43,54,62,72,80],[-10,77,80,94,96,98,101],[-45,94,96,98,101],[-59,80,96,98,101],[-62,77,94,101],[-98,10,45,59,77,94],[-101,10,45,59,62,77,80],[-11,12,27,30,32,73,74,75],[-12,11,25,30,32,69,71,75],[-25,12,73,74,75],[-27,11,69,71,75],[-69,12,27,32,73,74],[-71,12,27,30,32,73],[-73,11,25,30,69,71,75],[-74,11,25,30,32,69],[-25,13,76,78,79],[-36,11,66,71,76],[-71,13,34,36,39,78],[-78,11,25,34,66,71,76],[-79,11,25,34,39,66],[-11,17,48,51,83,85,86,88,89],[-25,17,83,85,86,88,89],[-66,17,51,86,88,89],[-69,17,48,83,85,89],[-85,11,25,51,69,86],[-88,11,25,48,66,83],[-89,11,25,48,51,66,69],[-12,14,34,41,44,76,81,82],[-27,14,76,81,82],[-44,12,66,74,76,82],[-66,14,41,44,81,82],[-74,14,34,41,44,81],[-81,12,27,34,66,74,76],[-27,19,83,85,90,91],[-66,19,56,90,91],[-73,19,48,83,85,91],[-85,12,27,56,73,90],[-91,12,27,48,56,66,73],[-36,15,75,81,82],[-46,13,69,75,79,82],[-69,15,41,46,81,82],[-79,15,30,41,46,81],[-81,13,30,36,69,75,79],[-13,21,51,61,86,88,94,95],[-21,13,36,51,61,69,78,86,94],[-36,21,86,88,94,95],[-69,21,61,94,95],[-78,21,51,86,88,95],[-88,13,36,61,78,94],[-95,13,36,51,61,69,78],[-14,15,32,39,46,78],[-44,15,78],[-46,14,73],[-73,15,39,46,78],[-78,14,32,44,73],[-14,56,64,90,96,99,100],[-44,90,96,99,100],[-73,64,96,99,100],[-81,56,90,100],[-96,14,44,56,73],[-99,14,44,56,73,90],[-100,14,44,56,64,73,81],[-15,61,64,94,96,99,101],[-46,94,96,99,101],[-78,64,96,99,101],[-81,61,94,101],[-96,15,46,61,78],[-99,15,46,61,78,94],[-101,15,46,61,64,78,81],[-17,16,49,52,53,67,70,84,87],[-53,17,67,70,71,85,88],[-71,16,49,52,53,84,87],[-84,17,52,70,71,88],[-85,16,52,53,70,87],[-87,17,49,67,71,85],[-88,16,49,53,67,84],[-16,18,55,57,91,92],[-18,16,53,57,87,89,92],[-53,18,91,92],[-55,16,87,89,92],[-89,18,55,57],[-91,16,53,57,87],[-20,16,53,58,84,89,93],[-53,20,93,95],[-60,16,84,89,93],[-84,20,60,95],[-89,20,58,60],[-95,16,53,58,84],[-19,17,71,75,88,89,92],[-71,19,91,92],[-74,17,88,89,92],[-88,19,74,91],[-89,19,74,75],[-91,17,71,75,88],[-21,17,71,76,85,89,93],[-71,21,93,95],[-79,17,85,89,93],[-85,21,79,95],[-89,21,76,79],[-95,17,71,76,85],[-18,19,49,67,74,85],[-55,19,67,74,85],[-74,18,49,55,84],[-84,19,74],[-85,18,55],[-18,58,63,93,97,98,100],[-55,93,97,98,100],[-84,63,97,98,100],[-91,58,63,98],[-97,18,55,58,84],[-100,18,55,58,63,84],[-19,76,82,93,97,99,100],[-74,93,97,99,100],[-85,82,97,99,100],[-91,76,82,99],[-97,19,74,76,85],[-99,19,74,76,85,91,93],[-100,19,74,76,82,85],[-20,21,52,70,79,88],[-60,21,70,79,88],[-79,20,52,60,87],[-87,21,79],[-88,20,60],[-20,57,63,92,97,98,101],[-60,92,97,98,101],[-87,63,97,98,101],[-95,57,63,98],[-97,20,57,60,87],[-98,20,57,60,87,92,95],[-101,20,57,60,63,87],[-21,75,82,92,97,99,101],[-79,92,97,99,101],[-88,82,97,99,101],[-95,75,82,99],[-97,21,75,79,88],[-99,21,75,79,88,92,95],[-101,21,75,79,82,88],[-29,68],[-68,29],[-30,51],[-51,30],[-31,72],[-72,31],[-32,56],[-56,32],[-33,65],[-65,33],[-34,48],[-48,34],[-38,77],[-77,38],[-39,61],[-61,39],[-40,80],[-80,40],[-41,64],[-64,41],[-49,58],[-58,49],[-52,57],[-57,52],[-63],[-67,76],[-76,67],[-70,75],[-75,70],[-82],[-83,93],[-93,83],[-86,92],[-92,86],[-90],[-94],[-98,99],[-99,98],[-100,101],[-101,100],[-1,102],[-2,103],[-3,104],[-4,105],[-5,106],[-6,107],[-7,108],[-109,8],[-8,109],[-110,9],[-9,110],[-111,10],[-10,111],[-11,112],[-12,113],[-13,114],[-14,115],[-15,116],[-16,117],[-17,118],[-18,119],[-19,120],[-20,121],[-21,122],[-103,123],[-102,123],[-106,124],[-105,124],[-105,-106,125],[-124,126],[-125,127],[-104,126],[-104,-124,127],[-126,128],[-127,129],[-123,128],[-123,-126,129],[-108,130],[-107,130],[-107,-108,131],[-132,110,111],[-111,132],[-110,132],[-110,-111,133],[-134,109,132],[-132,134],[-133,135],[-109,134],[-109,-132,135],[-109,-133,136],[-134,137],[-135,138],[-136,139],[-130,137],[-130,-134,138],[-130,-135,139],[-130,-136,140],[-131,138],[-131,-134,139],[-137,141],[-139,143],[-128,141],[-128,-137,142],[-128,-138,143],[-128,-139,144],[-128,-140,145],[-129,142],[-129,-137,143],[-129,-139,145],[-113,146],[-112,146],[-112,-113,147],[-116,148],[-115,148],[-115,-116,149],[-148,150],[-149,151],[-114,150],[-114,-148,151],[-114,-149,152],[-150,153],[-151,154],[-146,153],[-146,-150,154],[-146,-151,155],[-146,-152,156],[-147,154],[-147,-150,155],[-119,157],[-118,157],[-118,-119,158],[-157,159],[-158,160],[-117,159],[-117,-157,160],[-122,161],[-121,161],[-121,-122,162],[-161,163],[-162,164],[-120,163],[-120,-161,164],[-120,-162,165],[-163,166],[-164,167],[-159,166],[-159,-163,167],[-159,-164,168],[-159,-165,169],[-160,167],[-160,-163,168],[-160,-164,169],[-168,172],[-169,173],[-153,170],[-153,-166,171],[-153,-167,172],[-153,-168,173],[-153,-169,174],[-154,171],[-154,-166,172],[-154,-167,173],[-154,-168,174],[-154,-169,175],[-155,172],[-155,-166,173],[-155,-167,174],[-155,-168,175],[-156,173],[-175,176],[-141,-174,176],[-142,-173,176],[-143,-172,176],[-144,-171,176],[-145,-170,176],[-176],[-177,42,62,81],[-42,177],[-62,177],[-81,177],[-178,89,91,95],[-89,178],[-91,178],[-95,178],[-179,53,55,60],[-53,179],[-55,179],[-60,179],[-180,28,54,73],[-28,180],[-54,180],[-73,180],[-181,37,59,78],[-37,181],[-59,181],[-78,181],[-182,71,74,79],[-71,182],[-74,182],[-79,182],[-183,22,47,66,84,85],[-22,183],[-47,183],[-84,183],[-85,183],[-184,25,27,36,44,46],[-25,184],[-27,184],[-36,184],[-44,184],[-46,184],[-185,24,26,35,43,45],[-24,185],[-26,185],[-35,185],[-43,185],[-45,185],[-186,23,50,69,87,88],[-23,186],[-69,186],[-88,186],[-187,177,178],[-178,187],[-188,177],[-177,187],[-188,178],[-177,-178,188],[-189,180,181],[-190,180],[-190,181],[-180,-181,190],[-191,179,190],[-192,179],[-191,189],[-192,190],[-179,-190,192],[-193,187,192],[-194,187],[-193,188,191],[-194,188,192],[-187,-192,194],[-195,188],[-194,191],[-195,192],[-196,182,183],[-197,182],[-197,183],[-182,-183,197],[-198,185,186],[-199,185],[-199,186],[-200,184,199],[-201,184],[-200,198],[-201,199],[-184,-199,201],[-202,196],[-202,197,201],[-203,197],[-202,200],[-203,201],[-197,-201,203],[-204,193],[-204,194,203],[-204,195,202],[-194,-203,205],[204],[-205],[-206,96,98,100],[-96,206],[-98,206],[-100,206],[-207,97,99,101],[-97,207],[-99,207],[-101,207],[-208,29,31,33,38,40],[-29,208],[-31,208],[-33,208],[-38,208],[-40,208],[-209,30,32,34,39,41],[-30,209],[-32,209],[-34,209],[-39,209],[-41,209],[-210,49,52,63],[-49,210],[-52,210],[-211,48,58,65,67,83],[-48,211],[-58,211],[-65,211],[-67,211],[-83,211],[-212,51,56,61,64],[-51,212],[-56,212],[-61,212],[-64,212],[-213,70,76,82],[-70,213],[-76,213],[-214,68,72,77,80],[-68,214],[-72,214],[-77,214],[-80,214],[-215,57,75,86],[-57,215],[-75,215],[-86,215],[-216,90,92,93,94],[-92,216],[-93,216],[-207,217],[-218,206],[-206,217],[-218,207],[-219,209,210],[-210,219],[-209,219],[-220,208,219],[-219,220],[-208,220],[-220,221],[-217,221],[-222,218,220],[-217,-220,222],[-223,212,213],[-213,223],[-212,223],[-224,211,223],[-223,224],[-211,224],[-211,-223,225],[-226,215,216],[-216,226],[-215,226],[-215,-216,227],[-228,214,226],[-226,228],[-227,229],[-214,228],[-230,224,228],[-228,230],[-229,231],[-224,230],[-224,-228,231],[-225,231],[-232,222,230],[-221,-231,233],[-222,-230,233],[232],[-233],[-4,-8,-14,-18,-19,-23,-27,-45,-53,-54,-71,-78,-95,-98,-99],[-2,-7,-13,-18,-19,-23,-43,-46,-53,-59,-71,-73,-95,-98,-99],[-2,-6,-9,-10,-21,-25,-35,-42,-55,-73,-78,-85,-87,-100,-101],[-2,-10,-15,-18,-19,-24,-37,-44,-54,-60,-66,-79,-89,-98,-99],[-2,-8,-17,-18,-19,-23,-44,-45,-53,-54,-66,-78,-95,-98,-99],[-2,-6,-9,-10,-15,-25,-35,-42,-55,-73,-79,-85,-87,-100,-101],[-2,-7,-13,-20,-21,-23,-43,-46,-53,-59,-71,-73,-91,-98,-99],[-2,-8,-17,-20,-21,-23,-44,-45,-53,-54,-66,-78,-91,-98,-99],[-4,-8,-14,-20,-21,-23,-27,-45,-53,-54,-71,-78,-91,-98,-99],[-4,-9,-15,-16,-19,-22,-36,-45,-50,-55,-71,-73,-95,-98,-99],[-2,-10,-15,-16,-20,-25,-37,-43,-50,-55,-73,-79,-85,-96,-97],[-2,-6,-8,-10,-15,-25,-37,-43,-55,-73,-79,-85,-87,-96,-97],[-2,-4,-5,-6,-21,-25,-35,-55,-62,-73,-78,-85,-87,-100,-101],[-2,-5,-10,-16,-21,-23,-43,-47,-60,-71,-73,-78,-91,-98,-99],[-2,-8,-15,-17,-20,-23,-44,-45,-53,-54,-66,-79,-91,-98,-99],[-2,-3,-4,-9,-16,-25,-45,-50,-55,-73,-78,-85,-95,-98,-99],[-2,-3,-4,-9,-16,-25,-45,-47,-60,-73,-78,-88,-91,-98,-99],[-2,-8,-10,-15,-17,-24,-37,-44,-54,-69,-74,-84,-95,-98,-99],[-2,-8,-10,-15,-17,-24,-37,-44,-54,-66,-79,-87,-91,-98,-99],[-2,-8,-10,-15,-17,-25,-37,-43,-47,-73,-79,-87,-91,-98,-99],[-2,-10,-15,-16,-17,-24,-37,-44,-54,-60,-66,-79,-91,-98,-99],[-2,-6,-8,-10,-15,-25,-37,-43,-55,-73,-79,-85,-87,-98,-99],[-2,-10,-15,-16,-20,-25,-37,-43,-50,-55,-73,-79,-85,-98,-99],[-2,-10,-15,-18,-21,-24,-37,-44,-54,-60,-69,-74,-89,-98,-99],[-2,-10,-15,-16,-20,-25,-37,-43,-50,-55,-73,-79,-85,-100,-101],[-2,-6,-8,-10,-15,-25,-37,-43,-55,-73,-79,-85,-87,-100,-101],[-2,-6,-10,-14,-20,-25,-35,-42,-54,-74,-78,-84,-88,-100,-101],[-2,-9,-15,-19,-21,-24,-36,-42,-55,-59,-71,-73,-87,-100,-101],[-2,-4,-9,-16,-21,-23,-45,-47,-60,-71,-73,-78,-91,-98,-99],[-2,-7,-14,-17,-20,-23,-43,-46,-53,-59,-66,-79,-91,-98,-99],[-4,-9,-14,-16,-21,-23,-27,-45,-47,-60,-71,-78,-91,-98,-99],[-4,-8,-15,-18,-20,-25,-26,-37,-53,-62,-73,-79,-85,-100,-101],[-2,-8,-15,-17,-19,-24,-37,-44,-55,-62,-66,-79,-87,-100,-101],[-2,-6,-7,-10,-13,-25,-37,-43,-60,-74,-81,-84,-88,-100,-101],[-2,-7,-15,-17,-21,-24,-37,-44,-60,-62,-69,-74,-84,-100,-101],[-2,-6,-8,-10,-12,-25,-37,-43,-55,-79,-81,-85,-87,-100,-101],[-1,-2,-5,-10,-20,-35,-44,-53,-54,-66,-78,-88,-91,-98,-99],[-1,-2,-3,-7,-18,-43,-46,-53,-59,-69,-73,-85,-95,-98,-99],[-2,-3,-4,-6,-14,-25,-45,-54,-60,-74,-78,-84,-88,-96,-97],[-2,-3,-4,-6,-14,-25,-45,-54,-60,-74,-78,-84,-88,-98,-99],[-2,-3,-4,-9,-16,-24,-46,-55,-59,-69,-73,-85,-95,-98,-99],[-2,-4,-10,-17,-21,-24,-37,-54,-60,-69,-74,-81,-84,-100,-101],[-2,-4,-6,-10,-13,-25,-37,-54,-60,-74,-81,-84,-88,-100,-101],[-2,-3,-6,-9,-15,-25,-42,-55,-59,-73,-79,-85,-87,-100,-101],[-2,-3,-4,-6,-14,-25,-45,-54,-60,-74,-78,-84,-88,-100,-101],[-2,-4,-5,-6,-15,-25,-35,-55,-62,-73,-79,-85,-87,-100,-101],[-2,-4,-6,-8,-15,-25,-37,-55,-62,-73,-79,-85,-87,-100,-101],[-1,-2,-3,-6,-11,-43,-46,-55,-59,-73,-79,-85,-87,-96,-97],[-1,-2,-3,-6,-11,-43,-46,-55,-59,-73,-79,-85,-87,-98,-99],[-1,-2,-3,-6,-16,-43,-46,-55,-59,-69,-73,-85,-95,-98,-99],[-2,-3,-4,-6,-13,-25,-45,-54,-60,-74,-81,-84,-88,-100,-101],[-5,-7,-15,-20,-21,-22,-36,-43,-53,-59,-71,-73,-91,-98,-99],[-4,-9,-13,-18,-19,-23,-26,-46,-53,-59,-71,-73,-95,-98,-99],[-5,-10,-12,-20,-21,-22,-35,-44,-53,-54,-71,-78,-91,-98,-99],[-9,-10,-12,-16,-20,-25,-28,-37,-50,-55,-79,-81,-85,-100,-101],[-9,-10,-13,-16,-18,-25,-28,-37,-47,-60,-74,-81,-88,-100,-101],[-7,-14,-15,-17,-21,-24,-28,-37,-60,-62,-69,-74,-84,-100,-101],[-8,-14,-15,-17,-19,-24,-28,-37,-55,-62,-66,-79,-87,-100,-101],[-3,-8,-12,-20,-21,-22,-44,-45,-53,-54,-71,-78,-91,-98,-99],[-2,-8,-12,-18,-19,-23,-44,-45,-53,-54,-71,-78,-95,-98,-99],[-3,-7,-13,-20,-21,-22,-43,-46,-53,-59,-71,-73,-91,-98,-99],[-6,-7,-9,-10,-13,-25,-28,-37,-60,-74,-81,-84,-88,-100,-101],[-6,-8,-9,-10,-12,-25,-28,-37,-55,-79,-81,-85,-87,-100,-101],[-8,-11,-12,-14,-15,-24,-28,-37,-55,-62,-79,-85,-87,-100,-101],[-7,-11,-13,-14,-15,-24,-28,-37,-60,-62,-74,-84,-88,-100,-101],[-3,-6,-9,-10,-19,-25,-26,-42,-60,-73,-78,-84,-88,-100,-101],[-2,-11,-14,-15,-20,-24,-36,-42,-54,-59,-74,-84,-88,-100,-101],[-3,-11,-14,-15,-18,-24,-27,-42,-54,-59,-79,-85,-87,-100,-101],[-2,-6,-15,-18,-19,-23,-44,-45,-54,-60,-66,-79,-89,-98,-99],[-3,-6,-14,-20,-21,-22,-43,-46,-55,-59,-69,-74,-89,-98,-99],[-2,-10,-11,-18,-19,-23,-43,-46,-47,-60,-73,-79,-89,-98,-99],[-3,-9,-11,-20,-21,-22,-44,-45,-50,-55,-74,-78,-89,-98,-99],[-3,-9,-14,-20,-21,-24,-28,-46,-55,-59,-69,-74,-89,-98,-99],[-2,-10,-15,-18,-19,-25,-37,-43,-47,-60,-73,-79,-89,-98,-99],[-3,-9,-14,-20,-21,-25,-28,-45,-50,-55,-74,-78,-89,-98,-99],[-6,-9,-10,-19,-21,-22,-35,-42,-55,-71,-73,-78,-87,-100,-101],[-6,-9,-10,-19,-21,-23,-26,-42,-60,-71,-73,-78,-84,-100,-101],[-11,-14,-15,-18,-20,-22,-36,-42,-53,-54,-59,-74,-88,-100,-101],[-11,-14,-15,-18,-20,-23,-27,-42,-53,-54,-59,-79,-85,-100,-101],[-3,-7,-17,-20,-21,-22,-43,-46,-53,-59,-69,-73,-91,-98,-99],[-2,-13,-16,-18,-19,-23,-43,-46,-47,-59,-71,-73,-95,-98,-99],[-3,-12,-16,-20,-21,-22,-44,-45,-50,-54,-71,-78,-91,-98,-99],[-5,-6,-9,-10,-12,-25,-28,-35,-55,-79,-81,-85,-87,-100,-101],[-4,-6,-9,-10,-13,-25,-26,-37,-60,-74,-81,-84,-88,-100,-101],[-5,-7,-11,-14,-15,-24,-28,-36,-60,-62,-74,-84,-88,-100,-101],[-4,-8,-11,-14,-15,-24,-27,-37,-55,-62,-79,-85,-87,-100,-101],[-3,-6,-9,-10,-14,-25,-26,-42,-60,-74,-78,-84,-88,-100,-101],[-2,-10,-11,-14,-15,-24,-36,-42,-54,-60,-74,-84,-88,-100,-101],[-3,-9,-11,-14,-15,-24,-27,-42,-55,-59,-79,-85,-87,-100,-101],[-2,-6,-18,-19,-21,-23,-44,-45,-54,-60,-66,-78,-89,-98,-99],[-3,-6,-19,-20,-21,-22,-43,-46,-55,-59,-69,-73,-89,-98,-99],[-2,-11,-18,-19,-20,-23,-43,-46,-47,-59,-73,-79,-89,-98,-99],[-3,-11,-18,-20,-21,-22,-44,-45,-50,-54,-74,-78,-89,-98,-99],[-3,-8,-12,-18,-19,-22,-44,-45,-53,-54,-71,-78,-95,-98,-99],[-2,-8,-12,-20,-21,-23,-44,-45,-53,-54,-71,-78,-91,-98,-99],[-3,-7,-13,-18,-19,-22,-43,-46,-53,-59,-71,-73,-95,-98,-99],[-6,-7,-13,-14,-15,-25,-28,-37,-60,-62,-74,-84,-88,-100,-101],[-6,-8,-12,-14,-15,-25,-28,-37,-55,-62,-79,-85,-87,-100,-101],[-8,-9,-10,-11,-12,-24,-28,-37,-55,-79,-81,-85,-87,-100,-101],[-7,-9,-10,-11,-13,-24,-28,-37,-60,-74,-81,-84,-88,-100,-101],[-3,-7,-17,-18,-19,-22,-43,-46,-53,-59,-69,-73,-95,-98,-99],[-2,-13,-16,-20,-21,-23,-43,-46,-47,-59,-71,-73,-91,-98,-99],[-3,-12,-16,-18,-19,-22,-44,-45,-50,-54,-71,-78,-95,-98,-99],[-5,-6,-12,-14,-15,-25,-28,-35,-55,-62,-79,-85,-87,-100,-101],[-4,-6,-13,-14,-15,-25,-26,-37,-60,-62,-74,-84,-88,-100,-101],[-5,-7,-9,-10,-11,-24,-28,-36,-60,-74,-81,-84,-88,-100,-101],[-4,-8,-9,-10,-11,-24,-27,-37,-55,-79,-81,-85,-87,-100,-101],[-5,-7,-15,-18,-19,-22,-36,-43,-53,-59,-71,-73,-95,-98,-99],[-4,-9,-13,-20,-21,-23,-26,-46,-53,-59,-71,-73,-91,-98,-99],[-5,-10,-12,-18,-19,-22,-35,-44,-53,-54,-71,-78,-95,-98,-99],[-12,-14,-15,-16,-20,-25,-28,-37,-50,-55,-62,-79,-85,-100,-101],[-13,-14,-15,-16,-18,-25,-28,-37,-47,-60,-62,-74,-88,-100,-101],[-7,-9,-10,-17,-21,-24,-28,-37,-60,-69,-74,-81,-84,-100,-101],[-8,-9,-10,-17,-19,-24,-28,-37,-55,-66,-79,-81,-87,-100,-101],[-5,-10,-14,-16,-21,-23,-27,-43,-47,-60,-71,-78,-91,-98,-99],[-4,-10,-14,-17,-18,-22,-35,-46,-53,-54,-69,-74,-95,-98,-99],[-5,-9,-15,-17,-20,-23,-26,-44,-53,-59,-66,-79,-91,-98,-99],[-4,-10,-16,-18,-21,-24,-27,-37,-54,-60,-69,-81,-85,-100,-101],[-5,-9,-16,-19,-20,-24,-28,-36,-55,-59,-66,-81,-88,-100,-101],[-4,-15,-17,-19,-20,-25,-26,-37,-50,-62,-73,-79,-84,-100,-101],[-5,-14,-17,-18,-21,-25,-28,-35,-47,-62,-74,-78,-87,-100,-101],[-3,-9,-14,-16,-18,-25,-28,-45,-47,-60,-74,-78,-88,-96,-97],[-2,-10,-15,-17,-21,-24,-37,-44,-54,-60,-69,-74,-84,-96,-97],[-3,-9,-14,-17,-19,-24,-28,-46,-55,-59,-66,-79,-87,-96,-97],[-4,-6,-14,-19,-21,-23,-27,-45,-54,-60,-71,-78,-84,-96,-97],[-5,-6,-15,-19,-21,-22,-36,-43,-55,-59,-71,-73,-87,-96,-97],[-4,-9,-11,-18,-20,-23,-26,-46,-53,-59,-73,-79,-85,-96,-97],[-5,-10,-11,-18,-20,-22,-35,-44,-53,-54,-74,-78,-88,-96,-97],[-3,-6,-7,-9,-14,-25,-28,-45,-60,-74,-78,-84,-88,-96,-97],[-2,-10,-11,-13,-15,-24,-37,-44,-54,-60,-74,-84,-88,-96,-97],[-3,-9,-11,-12,-14,-24,-28,-46,-55,-59,-79,-85,-87,-96,-97],[-2,-6,-12,-19,-21,-23,-44,-45,-54,-60,-71,-78,-84,-96,-97],[-3,-6,-13,-19,-21,-22,-43,-46,-55,-59,-71,-73,-87,-96,-97],[-2,-7,-11,-18,-20,-23,-43,-46,-53,-59,-73,-79,-85,-96,-97],[-3,-8,-11,-18,-20,-22,-44,-45,-53,-54,-74,-78,-88,-96,-97],[-3,-4,-5,-6,-19,-25,-26,-60,-62,-73,-78,-84,-88,-100,-101],[-2,-4,-5,-11,-20,-24,-36,-54,-59,-74,-81,-84,-88,-100,-101],[-3,-4,-5,-11,-18,-24,-27,-54,-59,-79,-81,-85,-87,-100,-101],[-2,-6,-15,-16,-17,-23,-44,-45,-54,-60,-66,-79,-91,-98,-99],[-3,-6,-14,-16,-17,-22,-43,-46,-55,-59,-69,-74,-95,-98,-99],[-2,-10,-11,-16,-17,-23,-43,-46,-47,-60,-73,-79,-91,-98,-99],[-3,-9,-11,-16,-17,-22,-44,-45,-50,-55,-74,-78,-95,-98,-99],[-3,-4,-9,-16,-19,-22,-45,-50,-55,-71,-73,-78,-95,-98,-99],[-2,-5,-15,-17,-20,-23,-44,-53,-54,-59,-66,-79,-91,-98,-99],[-3,-4,-14,-17,-18,-22,-46,-53,-54,-59,-69,-74,-95,-98,-99],[-4,-6,-15,-17,-19,-25,-26,-37,-60,-62,-73,-79,-84,-100,-101],[-5,-6,-14,-17,-21,-25,-28,-35,-55,-62,-74,-78,-87,-100,-101],[-4,-10,-11,-16,-18,-24,-27,-37,-54,-60,-79,-81,-85,-100,-101],[-5,-9,-11,-16,-20,-24,-28,-36,-55,-59,-74,-81,-88,-100,-101],[-3,-7,-14,-17,-18,-22,-43,-46,-53,-59,-69,-74,-95,-98,-99],[-2,-10,-13,-16,-21,-23,-43,-46,-47,-60,-71,-73,-91,-98,-99],[-3,-9,-12,-16,-19,-22,-44,-45,-50,-55,-71,-78,-95,-98,-99],[-5,-6,-12,-14,-21,-25,-28,-35,-55,-62,-78,-85,-87,-100,-101],[-4,-6,-13,-15,-19,-25,-26,-37,-60,-62,-73,-84,-88,-100,-101],[-5,-7,-9,-11,-20,-24,-28,-36,-59,-74,-81,-84,-88,-100,-101],[-4,-8,-10,-11,-18,-24,-27,-37,-54,-79,-81,-85,-87,-100,-101],[-2,-3,-5,-10,-16,-25,-43,-47,-60,-73,-78,-88,-91,-98,-99],[-2,-3,-4,-14,-17,-24,-46,-54,-59,-69,-74,-84,-95,-98,-99],[-2,-3,-5,-15,-17,-24,-44,-54,-59,-66,-79,-87,-91,-98,-99],[-4,-6,-11,-16,-18,-23,-27,-45,-54,-60,-79,-81,-85,-100,-101],[-5,-6,-11,-16,-20,-22,-36,-43,-55,-59,-74,-81,-88,-100,-101],[-4,-6,-11,-17,-19,-23,-26,-46,-60,-62,-73,-79,-84,-100,-101],[-5,-6,-11,-17,-21,-22,-35,-44,-55,-62,-74,-78,-87,-100,-101],[-2,-3,-5,-10,-16,-25,-43,-50,-55,-73,-78,-85,-95,-98,-99],[-2,-3,-4,-14,-17,-24,-46,-54,-59,-66,-79,-87,-91,-98,-99],[-2,-3,-5,-15,-17,-24,-44,-54,-59,-69,-74,-84,-95,-98,-99],[-4,-6,-11,-16,-18,-23,-26,-46,-60,-62,-73,-79,-85,-100,-101],[-5,-6,-11,-16,-20,-22,-35,-44,-55,-62,-74,-78,-88,-100,-101],[-4,-6,-11,-17,-19,-23,-27,-45,-54,-60,-79,-81,-84,-100,-101],[-5,-6,-11,-17,-21,-22,-36,-43,-55,-59,-74,-81,-87,-100,-101],[-3,-7,-9,-14,-17,-24,-28,-46,-59,-66,-79,-87,-91,-98,-99],[-2,-10,-13,-15,-16,-25,-37,-43,-50,-55,-73,-85,-95,-98,-99],[-3,-9,-12,-14,-16,-25,-28,-45,-47,-60,-78,-88,-91,-98,-99],[-5,-6,-12,-19,-21,-22,-36,-43,-55,-59,-71,-81,-87,-100,-101],[-4,-6,-13,-19,-21,-23,-27,-45,-54,-60,-71,-81,-84,-100,-101],[-5,-7,-11,-18,-20,-22,-35,-44,-53,-62,-74,-78,-88,-100,-101],[-4,-8,-11,-18,-20,-23,-26,-46,-53,-62,-73,-79,-85,-100,-101],[-3,-7,-9,-14,-17,-24,-28,-46,-59,-69,-74,-84,-95,-98,-99],[-2,-10,-13,-15,-16,-25,-37,-43,-47,-60,-73,-88,-91,-98,-99],[-3,-9,-12,-14,-16,-25,-28,-45,-50,-55,-78,-85,-95,-98,-99],[-5,-6,-12,-19,-21,-22,-35,-44,-55,-62,-71,-78,-87,-100,-101],[-4,-6,-13,-19,-21,-23,-26,-46,-60,-62,-71,-73,-84,-100,-101],[-5,-7,-11,-18,-20,-22,-36,-43,-53,-59,-74,-81,-88,-100,-101],[-4,-8,-11,-18,-20,-23,-27,-45,-53,-54,-79,-81,-85,-100,-101],[-3,-7,-9,-14,-17,-25,-28,-45,-50,-74,-78,-84,-95,-98,-99],[-2,-10,-13,-15,-16,-24,-37,-44,-54,-60,-66,-88,-91,-98,-99],[-3,-9,-12,-14,-16,-24,-28,-46,-55,-59,-69,-85,-95,-98,-99],[-5,-6,-12,-19,-21,-23,-26,-44,-60,-62,-71,-78,-84,-100,-101],[-4,-6,-13,-19,-21,-22,-35,-46,-55,-62,-71,-73,-87,-100,-101],[-5,-7,-11,-18,-20,-23,-27,-43,-53,-59,-79,-81,-85,-100,-101],[-4,-8,-11,-18,-20,-22,-36,-45,-53,-54,-74,-81,-88,-100,-101],[-3,-9,-14,-16,-17,-24,-28,-46,-55,-59,-69,-74,-95,-98,-99],[-2,-10,-15,-16,-17,-25,-37,-43,-47,-60,-73,-79,-91,-98,-99],[-3,-9,-14,-16,-17,-25,-28,-45,-50,-55,-74,-78,-95,-98,-99],[-4,-5,-6,-19,-21,-22,-35,-55,-62,-71,-73,-78,-87,-100,-101],[-4,-5,-6,-19,-21,-23,-26,-60,-62,-71,-73,-78,-84,-100,-101],[-4,-5,-11,-18,-20,-22,-36,-53,-54,-59,-74,-81,-88,-100,-101],[-4,-5,-11,-18,-20,-23,-27,-53,-54,-59,-79,-81,-85,-100,-101],[-3,-6,-7,-9,-14,-25,-28,-45,-60,-74,-78,-84,-88,-98,-99],[-2,-10,-11,-13,-15,-24,-37,-44,-54,-60,-74,-84,-88,-98,-99],[-3,-9,-11,-12,-14,-24,-28,-46,-55,-59,-79,-85,-87,-98,-99],[-2,-6,-12,-19,-21,-23,-44,-45,-54,-60,-71,-78,-84,-100,-101],[-3,-6,-13,-19,-21,-22,-43,-46,-55,-59,-71,-73,-87,-100,-101],[-2,-7,-11,-18,-20,-23,-43,-46,-53,-59,-73,-79,-85,-100,-101],[-3,-8,-11,-18,-20,-22,-44,-45,-53,-54,-74,-78,-88,-100,-101],[-3,-9,-14,-16,-18,-25,-28,-45,-47,-60,-74,-78,-88,-98,-99],[-2,-10,-15,-17,-21,-24,-37,-44,-54,-60,-69,-74,-84,-98,-99],[-3,-9,-14,-17,-19,-24,-28,-46,-55,-59,-66,-79,-87,-98,-99],[-4,-6,-14,-19,-21,-23,-27,-45,-54,-60,-71,-78,-84,-100,-101],[-5,-6,-15,-19,-21,-22,-36,-43,-55,-59,-71,-73,-87,-100,-101],[-4,-9,-11,-18,-20,-23,-26,-46,-53,-59,-73,-79,-85,-100,-101],[-5,-10,-11,-18,-20,-22,-35,-44,-53,-54,-74,-78,-88,-100,-101],[-3,-9,-14,-19,-20,-24,-28,-46,-55,-59,-66,-79,-89,-98,-99],[-2,-10,-15,-19,-20,-25,-37,-43,-50,-55,-73,-79,-89,-98,-99],[-3,-9,-14,-18,-21,-25,-28,-45,-47,-60,-74,-78,-89,-98,-99],[-6,-9,-15,-19,-21,-22,-36,-42,-55,-59,-71,-73,-87,-100,-101],[-6,-10,-14,-19,-21,-23,-27,-42,-54,-60,-71,-78,-84,-100,-101],[-10,-11,-14,-18,-20,-22,-35,-42,-53,-54,-74,-78,-88,-100,-101],[-9,-11,-15,-18,-20,-23,-26,-42,-53,-59,-73,-79,-85,-100,-101],[-3,-9,-14,-16,-18,-25,-28,-45,-47,-60,-74,-78,-88,-100,-101],[-2,-10,-15,-17,-21,-24,-37,-44,-54,-60,-69,-74,-84,-100,-101],[-3,-9,-14,-17,-19,-24,-28,-46,-55,-59,-66,-79,-87,-100,-101],[-4,-6,-14,-19,-21,-23,-27,-45,-54,-60,-71,-78,-84,-98,-99],[-5,-6,-15,-19,-21,-22,-36,-43,-55,-59,-71,-73,-87,-98,-99],[-4,-9,-11,-18,-20,-23,-26,-46,-53,-59,-73,-79,-85,-98,-99],[-5,-10,-11,-18,-20,-22,-35,-44,-53,-54,-74,-78,-88,-98,-99],[-3,-6,-7,-9,-14,-25,-28,-45,-60,-74,-78,-84,-88,-100,-101],[-2,-10,-11,-13,-15,-24,-37,-44,-54,-60,-74,-84,-88,-100,-101],[-3,-9,-11,-12,-14,-24,-28,-46,-55,-59,-79,-85,-87,-100,-101],[-2,-6,-12,-19,-21,-23,-44,-45,-54,-60,-71,-78,-84,-98,-99],[-3,-6,-13,-19,-21,-22,-43,-46,-55,-59,-71,-73,-87,-98,-99],[-2,-7,-11,-18,-20,-23,-43,-46,-53,-59,-73,-79,-85,-98,-99],[-3,-8,-11,-18,-20,-22,-44,-45,-53,-54,-74,-78,-88,-98,-99],[-3,-6,-9,-15,-18,-25,-26,-42,-59,-73,-79,-85,-87,-100,-101],[-2,-9,-11,-15,-21,-24,-36,-42,-55,-59,-73,-85,-87,-100,-101],[-3,-10,-11,-14,-19,-24,-27,-42,-54,-60,-78,-84,-88,-100,-101],[-2,-6,-14,-19,-20,-23,-43,-46,-55,-59,-66,-79,-89,-98,-99],[-3,-6,-15,-18,-21,-22,-44,-45,-54,-60,-69,-74,-89,-98,-99],[-2,-9,-11,-18,-21,-23,-44,-45,-47,-60,-74,-78,-89,-98,-99],[-3,-10,-11,-19,-20,-22,-43,-46,-50,-55,-73,-79,-89,-98,-99],[-3,-10,-14,-19,-21,-24,-27,-42,-54,-60,-71,-78,-84,-100,-101],[-2,-10,-14,-18,-20,-25,-35,-42,-53,-54,-74,-78,-88,-100,-101],[-3,-9,-15,-18,-20,-25,-26,-42,-53,-59,-73,-79,-85,-100,-101],[-6,-10,-15,-18,-21,-22,-37,-44,-54,-60,-69,-74,-89,-98,-99],[-6,-9,-14,-19,-20,-23,-28,-46,-55,-59,-66,-79,-89,-98,-99],[-10,-11,-15,-19,-20,-22,-37,-43,-50,-55,-73,-79,-89,-98,-99],[-9,-11,-14,-18,-21,-23,-28,-45,-47,-60,-74,-78,-89,-98,-99],[-3,-5,-10,-16,-19,-22,-43,-50,-55,-71,-73,-78,-95,-98,-99],[-2,-4,-14,-17,-20,-23,-46,-53,-54,-59,-66,-79,-91,-98,-99],[-3,-5,-15,-17,-18,-22,-44,-53,-54,-59,-69,-74,-95,-98,-99],[-4,-6,-15,-16,-18,-25,-26,-37,-60,-62,-73,-79,-85,-100,-101],[-5,-6,-14,-16,-20,-25,-28,-35,-55,-62,-74,-78,-88,-100,-101],[-4,-10,-11,-17,-19,-24,-27,-37,-54,-60,-79,-81,-84,-100,-101],[-5,-9,-11,-17,-21,-24,-28,-36,-55,-59,-74,-81,-87,-100,-101],[-3,-8,-15,-17,-18,-22,-44,-45,-53,-54,-69,-74,-95,-98,-99],[-2,-9,-12,-16,-21,-23,-44,-45,-47,-60,-71,-78,-91,-98,-99],[-3,-10,-13,-16,-19,-22,-43,-46,-50,-55,-71,-73,-95,-98,-99],[-5,-6,-7,-14,-20,-25,-28,-35,-62,-74,-78,-84,-88,-100,-101],[-4,-6,-8,-15,-18,-25,-26,-37,-62,-73,-79,-85,-87,-100,-101],[-5,-9,-11,-12,-21,-24,-28,-36,-55,-59,-81,-85,-87,-100,-101],[-4,-10,-11,-13,-19,-24,-27,-37,-54,-60,-81,-84,-88,-100,-101],[-5,-10,-15,-16,-19,-22,-36,-43,-50,-55,-71,-73,-95,-98,-99],[-4,-9,-14,-17,-20,-23,-26,-46,-53,-59,-66,-79,-91,-98,-99],[-5,-10,-15,-17,-18,-22,-35,-44,-53,-54,-69,-74,-95,-98,-99],[-4,-15,-16,-18,-20,-25,-26,-37,-50,-62,-73,-79,-85,-100,-101],[-5,-14,-16,-18,-20,-25,-28,-35,-47,-62,-74,-78,-88,-100,-101],[-4,-10,-17,-19,-21,-24,-27,-37,-54,-60,-69,-81,-84,-100,-101],[-5,-9,-17,-19,-21,-24,-28,-36,-55,-59,-66,-81,-87,-100,-101],[-5,-7,-14,-18,-20,-25,-28,-35,-53,-62,-74,-78,-88,-100,-101],[-4,-10,-13,-19,-21,-24,-27,-37,-54,-60,-71,-81,-84,-100,-101],[-5,-9,-12,-19,-21,-24,-28,-36,-55,-59,-71,-81,-87,-100,-101],[-9,-12,-14,-16,-21,-23,-28,-45,-47,-60,-71,-78,-91,-98,-99],[-10,-13,-15,-16,-19,-22,-37,-43,-50,-55,-71,-73,-95,-98,-99],[-7,-9,-14,-17,-20,-23,-28,-46,-53,-59,-66,-79,-91,-98,-99],[-8,-10,-15,-17,-18,-22,-37,-44,-53,-54,-69,-74,-95,-98,-99],[-3,-7,-14,-17,-21,-24,-28,-46,-60,-62,-69,-74,-84,-100,-101],[-2,-10,-13,-16,-18,-25,-37,-43,-47,-60,-74,-81,-88,-100,-101],[-3,-9,-12,-16,-20,-25,-28,-45,-50,-55,-79,-81,-85,-100,-101],[-5,-6,-10,-12,-21,-22,-35,-44,-54,-71,-78,-87,-91,-98,-99],[-4,-6,-9,-13,-19,-23,-26,-46,-59,-71,-73,-84,-95,-98,-99],[-5,-7,-11,-15,-20,-22,-36,-43,-53,-59,-73,-88,-91,-98,-99],[-4,-8,-11,-14,-18,-23,-27,-45,-53,-54,-78,-85,-95,-98,-99],[-3,-6,-8,-9,-12,-25,-28,-45,-55,-79,-81,-85,-87,-100,-101],[-2,-8,-11,-12,-15,-24,-37,-44,-55,-62,-79,-85,-87,-100,-101],[-3,-7,-11,-13,-14,-24,-28,-46,-60,-62,-74,-84,-88,-100,-101],[-2,-6,-7,-13,-19,-23,-43,-46,-59,-71,-73,-84,-95,-98,-99],[-3,-6,-8,-12,-21,-22,-44,-45,-54,-71,-78,-87,-91,-98,-99],[-2,-8,-11,-12,-18,-23,-44,-45,-53,-54,-78,-85,-95,-98,-99],[-3,-7,-11,-13,-20,-22,-43,-46,-53,-59,-73,-88,-91,-98,-99],[-3,-8,-14,-17,-19,-24,-28,-46,-55,-62,-66,-79,-87,-100,-101],[-2,-10,-12,-16,-20,-25,-37,-43,-50,-55,-79,-81,-85,-100,-101],[-3,-9,-13,-16,-18,-25,-28,-45,-47,-60,-74,-81,-88,-100,-101],[-5,-6,-7,-15,-21,-22,-36,-43,-59,-71,-73,-87,-91,-98,-99],[-4,-6,-8,-14,-19,-23,-27,-45,-54,-71,-78,-84,-95,-98,-99],[-5,-10,-11,-12,-20,-22,-35,-44,-53,-54,-78,-88,-91,-98,-99],[-4,-9,-11,-13,-18,-23,-26,-46,-53,-59,-73,-85,-95,-98,-99],[-3,-6,-7,-9,-13,-25,-28,-45,-60,-74,-81,-84,-88,-100,-101],[-2,-7,-11,-13,-15,-24,-37,-44,-60,-62,-74,-84,-88,-100,-101],[-3,-8,-11,-12,-14,-24,-28,-46,-55,-62,-79,-85,-87,-100,-101],[-2,-6,-8,-12,-19,-23,-44,-45,-54,-71,-78,-84,-95,-98,-99],[-3,-6,-7,-13,-21,-22,-43,-46,-59,-71,-73,-87,-91,-98,-99],[-2,-7,-11,-13,-18,-23,-43,-46,-53,-59,-73,-85,-95,-98,-99],[-3,-8,-11,-12,-20,-22,-44,-45,-53,-54,-78,-88,-91,-98,-99],[-1,-3,-4,-9,-18,-26,-46,-53,-59,-69,-73,-85,-95,-98,-99],[-1,-2,-5,-15,-21,-36,-43,-47,-59,-71,-73,-87,-91,-98,-99],[-1,-3,-4,-14,-19,-27,-45,-50,-54,-71,-78,-84,-95,-98,-99],[-1,-6,-14,-17,-19,-28,-35,-46,-55,-62,-66,-79,-87,-100,-101],[-1,-6,-15,-17,-21,-26,-37,-44,-60,-62,-69,-74,-84,-100,-101],[-1,-9,-11,-16,-18,-28,-36,-45,-47,-60,-74,-81,-88,-100,-101],[-1,-10,-11,-16,-20,-27,-37,-43,-50,-55,-79,-81,-85,-100,-101],[-1,-2,-3,-8,-20,-44,-45,-53,-54,-66,-78,-88,-91,-98,-99],[-1,-2,-3,-12,-19,-44,-45,-50,-54,-71,-78,-84,-95,-98,-99],[-1,-2,-3,-13,-21,-43,-46,-47,-59,-71,-73,-87,-91,-98,-99],[-1,-6,-7,-9,-11,-28,-36,-45,-60,-74,-81,-84,-88,-100,-101],[-1,-6,-8,-10,-11,-27,-37,-43,-55,-79,-81,-85,-87,-100,-101],[-1,-6,-11,-12,-14,-28,-35,-46,-55,-62,-79,-85,-87,-100,-101],[-1,-6,-11,-13,-15,-26,-37,-44,-60,-62,-74,-84,-88,-100,-101],[-2,-3,-5,-6,-15,-25,-43,-55,-59,-73,-79,-85,-87,-96,-97],[-2,-3,-4,-9,-11,-24,-46,-55,-59,-73,-79,-85,-87,-96,-97],[-2,-3,-5,-10,-11,-24,-44,-54,-60,-74,-78,-84,-88,-96,-97],[-2,-6,-11,-16,-20,-23,-43,-46,-55,-59,-73,-79,-85,-96,-97],[-3,-6,-11,-16,-18,-22,-44,-45,-54,-60,-74,-78,-88,-96,-97],[-2,-6,-11,-17,-21,-23,-44,-45,-54,-60,-74,-78,-84,-96,-97],[-3,-6,-11,-17,-19,-22,-43,-46,-55,-59,-73,-79,-87,-96,-97],[-2,-3,-5,-6,-15,-25,-43,-55,-59,-73,-79,-85,-87,-98,-99],[-2,-3,-4,-9,-11,-24,-46,-55,-59,-73,-79,-85,-87,-98,-99],[-2,-3,-5,-10,-11,-24,-44,-54,-60,-74,-78,-84,-88,-98,-99],[-2,-6,-11,-16,-20,-23,-43,-46,-55,-59,-73,-79,-85,-100,-101],[-3,-6,-11,-16,-18,-22,-44,-45,-54,-60,-74,-78,-88,-100,-101],[-2,-6,-11,-17,-21,-23,-44,-45,-54,-60,-74,-78,-84,-100,-101],[-3,-6,-11,-17,-19,-22,-43,-46,-55,-59,-73,-79,-87,-100,-101],[-2,-3,-5,-10,-16,-24,-44,-54,-60,-66,-78,-88,-91,-98,-99],[-2,-3,-4,-14,-17,-25,-45,-50,-54,-74,-78,-84,-95,-98,-99],[-2,-3,-5,-15,-17,-25,-43,-47,-59,-73,-79,-87,-91,-98,-99],[-4,-6,-11,-16,-18,-22,-36,-45,-54,-60,-74,-81,-88,-100,-101],[-5,-6,-11,-16,-20,-23,-27,-43,-55,-59,-79,-81,-85,-100,-101],[-4,-6,-11,-17,-19,-22,-35,-46,-55,-62,-73,-79,-87,-100,-101],[-5,-6,-11,-17,-21,-23,-26,-44,-60,-62,-74,-78,-84,-100,-101],[-3,-5,-9,-17,-19,-24,-28,-55,-59,-66,-79,-81,-87,-100,-101],[-2,-4,-15,-16,-20,-25,-37,-50,-55,-62,-73,-79,-85,-100,-101],[-3,-5,-14,-16,-18,-25,-28,-47,-60,-62,-74,-78,-88,-100,-101],[-5,-6,-15,-16,-19,-22,-36,-43,-55,-59,-71,-73,-95,-98,-99],[-4,-6,-14,-16,-21,-23,-27,-45,-54,-60,-71,-78,-91,-98,-99],[-5,-10,-11,-17,-18,-22,-35,-44,-53,-54,-74,-78,-95,-98,-99],[-4,-9,-11,-17,-20,-23,-26,-46,-53,-59,-73,-79,-91,-98,-99],[-3,-5,-6,-9,-12,-25,-28,-55,-59,-79,-81,-85,-87,-100,-101],[-2,-4,-8,-11,-15,-24,-37,-55,-62,-73,-79,-85,-87,-100,-101],[-3,-5,-7,-11,-14,-24,-28,-60,-62,-74,-78,-84,-88,-100,-101],[-2,-6,-13,-16,-19,-23,-43,-46,-55,-59,-71,-73,-95,-98,-99],[-3,-6,-12,-16,-21,-22,-44,-45,-54,-60,-71,-78,-91,-98,-99],[-2,-8,-11,-17,-18,-23,-44,-45,-53,-54,-74,-78,-95,-98,-99],[-3,-7,-11,-17,-20,-22,-43,-46,-53,-59,-73,-79,-91,-98,-99],[-2,-3,-6,-10,-14,-25,-42,-54,-60,-74,-78,-84,-88,-100,-101],[-2,-3,-10,-11,-14,-24,-42,-54,-60,-74,-78,-84,-88,-100,-101],[-2,-3,-9,-11,-15,-24,-42,-55,-59,-73,-79,-85,-87,-100,-101],[-2,-6,-11,-18,-21,-23,-44,-45,-54,-60,-74,-78,-89,-98,-99],[-3,-6,-11,-19,-20,-22,-43,-46,-55,-59,-73,-79,-89,-98,-99],[-2,-6,-11,-19,-20,-23,-43,-46,-55,-59,-73,-79,-89,-98,-99],[-3,-6,-11,-18,-21,-22,-44,-45,-54,-60,-74,-78,-89,-98,-99],[-2,-3,-5,-6,-15,-25,-43,-55,-59,-73,-79,-85,-87,-100,-101],[-2,-3,-4,-9,-11,-24,-46,-55,-59,-73,-79,-85,-87,-100,-101],[-2,-3,-5,-10,-11,-24,-44,-54,-60,-74,-78,-84,-88,-100,-101],[-2,-6,-11,-16,-20,-23,-43,-46,-55,-59,-73,-79,-85,-98,-99],[-3,-6,-11,-16,-18,-22,-44,-45,-54,-60,-74,-78,-88,-98,-99],[-2,-6,-11,-17,-21,-23,-44,-45,-54,-60,-74,-78,-84,-98,-99],[-3,-6,-11,-17,-19,-22,-43,-46,-55,-59,-73,-79,-87,-98,-99],[-3,-4,-5,-6,-14,-25,-26,-60,-62,-74,-78,-84,-88,-100,-101],[-2,-4,-5,-10,-11,-24,-36,-54,-60,-74,-81,-84,-88,-100,-101],[-3,-4,-5,-9,-11,-24,-27,-55,-59,-79,-81,-85,-87,-100,-101],[-2,-6,-16,-17,-21,-23,-44,-45,-54,-60,-66,-78,-91,-98,-99],[-3,-6,-16,-17,-19,-22,-43,-46,-55,-59,-69,-73,-95,-98,-99],[-2,-11,-16,-17,-20,-23,-43,-46,-47,-59,-73,-79,-91,-98,-99],[-3,-11,-16,-17,-18,-22,-44,-45,-50,-54,-74,-78,-95,-98,-99],[-3,-5,-6,-7,-14,-25,-28,-60,-62,-74,-78,-84,-88,-100,-101],[-2,-4,-10,-11,-13,-24,-37,-54,-60,-74,-81,-84,-88,-100,-101],[-3,-5,-9,-11,-12,-24,-28,-55,-59,-79,-81,-85,-87,-100,-101],[-2,-6,-12,-16,-21,-23,-44,-45,-54,-60,-71,-78,-91,-98,-99],[-3,-6,-13,-16,-19,-22,-43,-46,-55,-59,-71,-73,-95,-98,-99],[-2,-7,-11,-17,-20,-23,-43,-46,-53,-59,-73,-79,-91,-98,-99],[-3,-8,-11,-17,-18,-22,-44,-45,-53,-54,-74,-78,-95,-98,-99],[-1,-2,-3,-6,-11,-44,-45,-54,-60,-74,-78,-84,-88,-96,-97],[-1,-2,-3,-6,-11,-44,-45,-54,-60,-74,-78,-84,-88,-98,-99],[-1,-2,-3,-6,-11,-44,-45,-54,-60,-74,-78,-84,-88,-100,-101],[-1,-2,-3,-6,-11,-43,-46,-55,-59,-73,-79,-85,-87,-100,-101],[-1,-2,-3,-6,-16,-44,-45,-54,-60,-66,-78,-88,-91,-98,-99],[-1,-2,-3,-11,-17,-44,-45,-50,-54,-74,-78,-84,-95,-98,-99],[-1,-2,-3,-11,-17,-43,-46,-47,-59,-73,-79,-87,-91,-98,-99],[-1,-2,-4,-6,-11,-36,-45,-54,-60,-74,-81,-84,-88,-100,-101],[-1,-3,-5,-6,-11,-27,-43,-55,-59,-79,-81,-85,-87,-100,-101],[-1,-2,-4,-6,-11,-35,-46,-55,-62,-73,-79,-85,-87,-100,-101],[-1,-3,-5,-6,-11,-26,-44,-60,-62,-74,-78,-84,-88,-100,-101],[-2,-3,-5,-6,-12,-25,-43,-55,-59,-79,-81,-85,-87,-100,-101],[-2,-3,-4,-8,-11,-24,-46,-55,-62,-73,-79,-85,-87,-100,-101],[-2,-3,-5,-7,-11,-24,-44,-60,-62,-74,-78,-84,-88,-100,-101],[-2,-6,-11,-13,-16,-23,-43,-46,-55,-59,-73,-85,-95,-98,-99],[-3,-6,-11,-12,-16,-22,-44,-45,-54,-60,-78,-88,-91,-98,-99],[-2,-6,-8,-11,-17,-23,-44,-45,-54,-74,-78,-84,-95,-98,-99],[-3,-6,-7,-11,-17,-22,-43,-46,-59,-73,-79,-87,-91,-98,-99],[18,19,49,55,58,63,67,74,76,82,84,85,91,93,97,98,99,100],[20,21,52,57,60,63,70,75,79,82,87,88,92,95,97,98,99,101],[9,10,31,38,43,45,54,59,62,72,77,80,90,94,96,98,100,101]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":1,\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":3,\"kind\":1},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":20,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":22,\"b\":21},{\"tag\":\"incompatible\",\"a\":23,\"b\":21},{\"tag\":\"incompatible\",\"a\":23,\"b\":22},{\"tag\":\"incompatible\",\"a\":24,\"b\":10},{\"tag\":\"incompatible\",\"a\":24,\"b\":21},{\"tag\":\"incompatible\",\"a\":24,\"b\":22},{\"tag\":\"incompatible\",\"a\":24,\"b\":23},{\"tag\":\"incompatible\",\"a\":25,\"b\":1},{\"tag\":\"incompatible\",\"a\":25,\"b\":21},{\"tag\":\"incompatible\",\"a\":26,\"b\":21},{\"tag\":\"incompatible\",\"a\":26,\"b\":24},{\"tag\":\"incompatible\",\"a\":26,\"b\":25},{\"tag\":\"incompatible\",\"a\":27,\"b\":1},{\"tag\":\"incompatible\",\"a\":27,\"b\":21},{\"tag\":\"incompatible\",\"a\":27,\"b\":25},{\"tag\":\"incompatible\",\"a\":27,\"b\":26},{\"tag\":\"incompatible\",\"a\":34,\"b\":2},{\"tag\":\"incompatible\",\"a\":34,\"b\":22},{\"tag\":\"incompatible\",\"a\":34,\"b\":23},{\"tag\":\"incompatible\",\"a\":34,\"b\":25},{\"tag\":\"incompatible\",\"a\":35,\"b\":2},{\"tag\":\"incompatible\",\"a\":35,\"b\":22},{\"tag\":\"incompatible\",\"a\":35,\"b\":24},{\"tag\":\"incompatible\",\"a\":35,\"b\":26},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":2},{\"tag\":\"incompatible\",\"a\":36,\"b\":4},{\"tag\":\"incompatible\",\"a\":36,\"b\":22},{\"tag\":\"incompatible\",\"a\":36,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":27},{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":42,\"b\":8},{\"tag\":\"incompatible\",\"a\":42,\"b\":23},{\"tag\":\"incompatible\",\"a\":42,\"b\":25},{\"tag\":\"incompatible\",\"a\":42,\"b\":27},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":24},{\"tag\":\"incompatible\",\"a\":43,\"b\":26},{\"tag\":\"incompatible\",\"a\":43,\"b\":27},{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":44,\"b\":9},{\"tag\":\"incompatible\",\"a\":44,\"b\":23},{\"tag\":\"incompatible\",\"a\":44,\"b\":25},{\"tag\":\"incompatible\",\"a\":44,\"b\":34},{\"tag\":\"incompatible\",\"a\":44,\"b\":36},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":4},{\"tag\":\"incompatible\",\"a\":45,\"b\":24},{\"tag\":\"incompatible\",\"a\":45,\"b\":26},{\"tag\":\"incompatible\",\"a\":45,\"b\":35},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":45,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":5},{\"tag\":\"incompatible\",\"a\":46,\"b\":21},{\"tag\":\"incompatible\",\"a\":46,\"b\":23},{\"tag\":\"incompatible\",\"a\":46,\"b\":25},{\"tag\":\"incompatible\",\"a\":49,\"b\":22},{\"tag\":\"incompatible\",\"a\":49,\"b\":23},{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":15},{\"tag\":\"incompatible\",\"a\":52,\"b\":23},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":8},{\"tag\":\"incompatible\",\"a\":53,\"b\":25},{\"tag\":\"incompatible\",\"a\":53,\"b\":27},{\"tag\":\"incompatible\",\"a\":53,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":25},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":22},{\"tag\":\"incompatible\",\"a\":56,\"b\":49},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":7},{\"tag\":\"incompatible\",\"a\":58,\"b\":9},{\"tag\":\"incompatible\",\"a\":58,\"b\":34},{\"tag\":\"incompatible\",\"a\":58,\"b\":36},{\"tag\":\"incompatible\",\"a\":58,\"b\":44},{\"tag\":\"incompatible\",\"a\":58,\"b\":49},{\"tag\":\"incompatible\",\"a\":59,\"b\":34},{\"tag\":\"incompatible\",\"a\":59,\"b\":49},{\"tag\":\"incompatible\",\"a\":59,\"b\":52},{\"tag\":\"incompatible\",\"a\":59,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":41},{\"tag\":\"incompatible\",\"a\":61,\"b\":42},{\"tag\":\"incompatible\",\"a\":61,\"b\":44},{\"tag\":\"incompatible\",\"a\":61,\"b\":53},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":10},{\"tag\":\"incompatible\",\"a\":65,\"b\":21},{\"tag\":\"incompatible\",\"a\":65,\"b\":24},{\"tag\":\"incompatible\",\"a\":65,\"b\":26},{\"tag\":\"incompatible\",\"a\":65,\"b\":46},{\"tag\":\"incompatible\",\"a\":68,\"b\":22},{\"tag\":\"incompatible\",\"a\":68,\"b\":24},{\"tag\":\"incompatible\",\"a\":68,\"b\":35},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":56},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":10},{\"tag\":\"incompatible\",\"a\":70,\"b\":24},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":72,\"b\":26},{\"tag\":\"incompatible\",\"a\":72,\"b\":27},{\"tag\":\"incompatible\",\"a\":72,\"b\":43},{\"tag\":\"incompatible\",\"a\":72,\"b\":53},{\"tag\":\"incompatible\",\"a\":72,\"b\":65},{\"tag\":\"incompatible\",\"a\":73,\"b\":26},{\"tag\":\"incompatible\",\"a\":73,\"b\":65},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":35},{\"tag\":\"incompatible\",\"a\":77,\"b\":36},{\"tag\":\"incompatible\",\"a\":77,\"b\":45},{\"tag\":\"incompatible\",\"a\":77,\"b\":58},{\"tag\":\"incompatible\",\"a\":77,\"b\":68},{\"tag\":\"incompatible\",\"a\":78,\"b\":12},{\"tag\":\"incompatible\",\"a\":78,\"b\":35},{\"tag\":\"incompatible\",\"a\":78,\"b\":68},{\"tag\":\"incompatible\",\"a\":78,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":80,\"b\":41},{\"tag\":\"incompatible\",\"a\":80,\"b\":43},{\"tag\":\"incompatible\",\"a\":80,\"b\":45},{\"tag\":\"incompatible\",\"a\":80,\"b\":61},{\"tag\":\"incompatible\",\"a\":80,\"b\":72},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":83,\"b\":15},{\"tag\":\"incompatible\",\"a\":83,\"b\":21},{\"tag\":\"incompatible\",\"a\":83,\"b\":46},{\"tag\":\"incompatible\",\"a\":83,\"b\":52},{\"tag\":\"incompatible\",\"a\":83,\"b\":54},{\"tag\":\"incompatible\",\"a\":83,\"b\":65},{\"tag\":\"incompatible\",\"a\":84,\"b\":18},{\"tag\":\"incompatible\",\"a\":84,\"b\":21},{\"tag\":\"incompatible\",\"a\":84,\"b\":46},{\"tag\":\"incompatible\",\"a\":84,\"b\":65},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":22},{\"tag\":\"incompatible\",\"a\":86,\"b\":49},{\"tag\":\"incompatible\",\"a\":86,\"b\":52},{\"tag\":\"incompatible\",\"a\":86,\"b\":56},{\"tag\":\"incompatible\",\"a\":86,\"b\":59},{\"tag\":\"incompatible\",\"a\":86,\"b\":68},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":22},{\"tag\":\"incompatible\",\"a\":87,\"b\":49},{\"tag\":\"incompatible\",\"a\":87,\"b\":56},{\"tag\":\"incompatible\",\"a\":87,\"b\":68},{\"tag\":\"incompatible\",\"a\":87,\"b\":70},{\"tag\":\"incompatible\",\"a\":87,\"b\":78},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"incompatible\",\"a\":88,\"b\":15},{\"tag\":\"incompatible\",\"a\":88,\"b\":51},{\"tag\":\"incompatible\",\"a\":88,\"b\":52},{\"tag\":\"incompatible\",\"a\":88,\"b\":70},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":88,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":17},{\"tag\":\"incompatible\",\"a\":90,\"b\":54},{\"tag\":\"incompatible\",\"a\":90,\"b\":73},{\"tag\":\"incompatible\",\"a\":90,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":84},{\"tag\":\"incompatible\",\"a\":94,\"b\":19},{\"tag\":\"incompatible\",\"a\":94,\"b\":51},{\"tag\":\"incompatible\",\"a\":94,\"b\":59},{\"tag\":\"incompatible\",\"a\":94,\"b\":78},{\"tag\":\"incompatible\",\"a\":94,\"b\":86},{\"tag\":\"incompatible\",\"a\":94,\"b\":87},{\"tag\":\"incompatible\",\"a\":94,\"b\":88},{\"tag\":\"incompatible\",\"a\":94,\"b\":90},{\"tag\":\"incompatible\",\"a\":95,\"b\":41},{\"tag\":\"incompatible\",\"a\":95,\"b\":88},{\"tag\":\"incompatible\",\"a\":96,\"b\":41},{\"tag\":\"incompatible\",\"a\":96,\"b\":88},{\"tag\":\"incompatible\",\"a\":97,\"b\":41},{\"tag\":\"incompatible\",\"a\":97,\"b\":61},{\"tag\":\"incompatible\",\"a\":97,\"b\":80},{\"tag\":\"incompatible\",\"a\":98,\"b\":41},{\"tag\":\"incompatible\",\"a\":98,\"b\":61},{\"tag\":\"incompatible\",\"a\":98,\"b\":80},{\"tag\":\"incompatible\",\"a\":99,\"b\":88},{\"tag\":\"incompatible\",\"a\":99,\"b\":90},{\"tag\":\"incompatible\",\"a\":99,\"b\":94},{\"tag\":\"incompatible\",\"a\":100,\"b\":88},{\"tag\":\"mate\",\"ridge\":7,\"a\":1,\"owners\":[0,22,23,24,28,29,30,31]},{\"tag\":\"mate\",\"ridge\":7,\"a\":22,\"owners\":[1,25,26,27,30,31]},{\"tag\":\"mate\",\"ridge\":7,\"a\":23,\"owners\":[1,26,27,29,31]},{\"tag\":\"mate\",\"ridge\":7,\"a\":24,\"owners\":[1,25,27,28,30]},{\"tag\":\"mate\",\"ridge\":7,\"a\":25,\"owners\":[0,22,24,29,31]},{\"tag\":\"mate\",\"ridge\":7,\"a\":26,\"owners\":[0,22,23,28,30]},{\"tag\":\"mate\",\"ridge\":7,\"a\":27,\"owners\":[0,22,23,24,28,29]},{\"tag\":\"mate\",\"ridge\":11,\"a\":21,\"owners\":[2,34,35,36,37,38]},{\"tag\":\"mate\",\"ridge\":11,\"a\":23,\"owners\":[2,33,35,36,38]},{\"tag\":\"mate\",\"ridge\":11,\"a\":24,\"owners\":[2,32,34,36,37]},{\"tag\":\"mate\",\"ridge\":11,\"a\":34,\"owners\":[0,21,24,33,38]},{\"tag\":\"mate\",\"ridge\":11,\"a\":35,\"owners\":[0,21,23,32,37]},{\"tag\":\"mate\",\"ridge\":11,\"a\":36,\"owners\":[0,21,23,24,32,33]},{\"tag\":\"mate\",\"ridge\":13,\"a\":0,\"owners\":[5,46,47,48,49,50,51,52]},{\"tag\":\"mate\",\"ridge\":13,\"a\":5,\"owners\":[0,21,22,24,47,48,50,51]},{\"tag\":\"mate\",\"ridge\":13,\"a\":21,\"owners\":[5,49,50,51,52]},{\"tag\":\"mate\",\"ridge\":13,\"a\":22,\"owners\":[5,46,47,48,52]},{\"tag\":\"mate\",\"ridge\":13,\"a\":24,\"owners\":[5,46,48,49,51,52]},{\"tag\":\"mate\",\"ridge\":13,\"a\":46,\"owners\":[0,22,24,50,51]},{\"tag\":\"mate\",\"ridge\":13,\"a\":49,\"owners\":[0,21,24,47,48]},{\"tag\":\"mate\",\"ridge\":13,\"a\":52,\"owners\":[0,21,22,24,47,50]},{\"tag\":\"mate\",\"ridge\":14,\"a\":21,\"owners\":[10,67,68,69,70]},{\"tag\":\"mate\",\"ridge\":14,\"a\":22,\"owners\":[10,64,65,66,70]},{\"tag\":\"mate\",\"ridge\":14,\"a\":23,\"owners\":[10,65,66,68,69,70]},{\"tag\":\"mate\",\"ridge\":14,\"a\":65,\"owners\":[0,22,23,67,69]},{\"tag\":\"mate\",\"ridge\":14,\"a\":68,\"owners\":[0,21,23,64,66]},{\"tag\":\"mate\",\"ridge\":19,\"a\":21,\"owners\":[3,39,40,41,42,43]},{\"tag\":\"mate\",\"ridge\":19,\"a\":25,\"owners\":[3,33,40,41,43]},{\"tag\":\"mate\",\"ridge\":19,\"a\":26,\"owners\":[3,32,39,41,42]},{\"tag\":\"mate\",\"ridge\":19,\"a\":41,\"owners\":[1,21,25,26,32,33]},{\"tag\":\"mate\",\"ridge\":19,\"a\":42,\"owners\":[1,21,26,33,40]},{\"tag\":\"mate\",\"ridge\":19,\"a\":43,\"owners\":[1,21,25,32,39]},{\"tag\":\"mate\",\"ridge\":21,\"a\":1,\"owners\":[6,46,47,48,53,54,55]},{\"tag\":\"mate\",\"ridge\":21,\"a\":21,\"owners\":[6,53,54,55]},{\"tag\":\"mate\",\"ridge\":21,\"a\":26,\"owners\":[6,46,48,53,54]},{\"tag\":\"mate\",\"ridge\":21,\"a\":27,\"owners\":[6,46,47,48,54]},{\"tag\":\"mate\",\"ridge\":21,\"a\":46,\"owners\":[1,26,27,55]},{\"tag\":\"mate\",\"ridge\":21,\"a\":53,\"owners\":[1,21,26,47,48]},{\"tag\":\"mate\",\"ridge\":21,\"a\":54,\"owners\":[1,21,26,27,47,55]},{\"tag\":\"mate\",\"ridge\":22,\"a\":21,\"owners\":[11,71,72,73]},{\"tag\":\"mate\",\"ridge\":22,\"a\":27,\"owners\":[11,64,65,66,73]},{\"tag\":\"mate\",\"ridge\":22,\"a\":72,\"owners\":[1,21,25,64,66]},{\"tag\":\"mate\",\"ridge\":22,\"a\":73,\"owners\":[1,21,25,27,64,71]},{\"tag\":\"mate\",\"ridge\":35,\"a\":2,\"owners\":[4,28,29,39,40,41,44,45]},{\"tag\":\"mate\",\"ridge\":35,\"a\":22,\"owners\":[4,39,40,41,44,45]},{\"tag\":\"mate\",\"ridge\":35,\"a\":34,\"owners\":[4,29,40,41,45]},{\"tag\":\"mate\",\"ridge\":35,\"a\":35,\"owners\":[4,28,39,41,44]},{\"tag\":\"mate\",\"ridge\":35,\"a\":41,\"owners\":[2,22,28,29,34,35]},{\"tag\":\"mate\",\"ridge\":35,\"a\":44,\"owners\":[2,22,29,35,40]},{\"tag\":\"mate\",\"ridge\":35,\"a\":45,\"owners\":[2,22,28,34,39]},{\"tag\":\"mate\",\"ridge\":41,\"a\":2,\"owners\":[7,49,50,51,58,59,60]},{\"tag\":\"mate\",\"ridge\":41,\"a\":22,\"owners\":[7,58,59,60]},{\"tag\":\"mate\",\"ridge\":41,\"a\":36,\"owners\":[7,49,50,51,59]},{\"tag\":\"mate\",\"ridge\":41,\"a\":49,\"owners\":[2,35,36,60]},{\"tag\":\"mate\",\"ridge\":41,\"a\":58,\"owners\":[2,22,35,50,51]},{\"tag\":\"mate\",\"ridge\":41,\"a\":59,\"owners\":[2,22,35,36,50,60]},{\"tag\":\"mate\",\"ridge\":42,\"a\":22,\"owners\":[12,76,77,78]},{\"tag\":\"mate\",\"ridge\":42,\"a\":34,\"owners\":[12,68,69,77,78]},{\"tag\":\"mate\",\"ridge\":42,\"a\":36,\"owners\":[12,67,68,69,78]},{\"tag\":\"mate\",\"ridge\":42,\"a\":68,\"owners\":[2,34,36,76]},{\"tag\":\"mate\",\"ridge\":42,\"a\":77,\"owners\":[2,22,34,67,69]},{\"tag\":\"mate\",\"ridge\":42,\"a\":78,\"owners\":[2,22,34,36,67,76]},{\"tag\":\"mate\",\"ridge\":259,\"a\":3,\"owners\":[4,30,31,36,37,38,44,45]},{\"tag\":\"mate\",\"ridge\":259,\"a\":27,\"owners\":[4,36,37,38,44,45]},{\"tag\":\"mate\",\"ridge\":259,\"a\":36,\"owners\":[3,27,30,31,42,43]},{\"tag\":\"mate\",\"ridge\":259,\"a\":42,\"owners\":[4,31,36,38,45]},{\"tag\":\"mate\",\"ridge\":259,\"a\":43,\"owners\":[4,30,36,37,44]},{\"tag\":\"mate\",\"ridge\":259,\"a\":44,\"owners\":[3,27,31,38,43]},{\"tag\":\"mate\",\"ridge\":259,\"a\":45,\"owners\":[3,27,30,37,42]},{\"tag\":\"mate\",\"ridge\":273,\"a\":8,\"owners\":[3,27,41,43,55,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":27,\"owners\":[8,61,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":41,\"owners\":[8,53,55]},{\"tag\":\"mate\",\"ridge\":273,\"a\":53,\"owners\":[3,41,43,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":61,\"owners\":[3,27,43,55]},{\"tag\":\"mate\",\"ridge\":274,\"a\":13,\"owners\":[3,27,41,42,71,79]},{\"tag\":\"mate\",\"ridge\":274,\"a\":27,\"owners\":[13,79,80]},{\"tag\":\"mate\",\"ridge\":274,\"a\":41,\"owners\":[13,71,72]},{\"tag\":\"mate\",\"ridge\":274,\"a\":42,\"owners\":[13,72,80]},{\"tag\":\"mate\",\"ridge\":274,\"a\":72,\"owners\":[3,41,42,79]},{\"tag\":\"mate\",\"ridge\":274,\"a\":80,\"owners\":[3,27,42,71]},{\"tag\":\"mate\",\"ridge\":289,\"a\":9,\"owners\":[4,36,41,45,60,63]},{\"tag\":\"mate\",\"ridge\":289,\"a\":36,\"owners\":[9,61,63]},{\"tag\":\"mate\",\"ridge\":289,\"a\":41,\"owners\":[9,58,60]},{\"tag\":\"mate\",\"ridge\":289,\"a\":45,\"owners\":[9,58,61]},{\"tag\":\"mate\",\"ridge\":289,\"a\":58,\"owners\":[4,41,45,63]},{\"tag\":\"mate\",\"ridge\":289,\"a\":61,\"owners\":[4,36,45,60]},{\"tag\":\"mate\",\"ridge\":290,\"a\":4,\"owners\":[14,76,77,79,80]},{\"tag\":\"mate\",\"ridge\":290,\"a\":14,\"owners\":[4,36,41,44,76,79]},{\"tag\":\"mate\",\"ridge\":290,\"a\":36,\"owners\":[14,79,80]},{\"tag\":\"mate\",\"ridge\":290,\"a\":41,\"owners\":[14,76,77]},{\"tag\":\"mate\",\"ridge\":290,\"a\":44,\"owners\":[14,77,80]},{\"tag\":\"mate\",\"ridge\":290,\"a\":77,\"owners\":[4,41,44,79]},{\"tag\":\"mate\",\"ridge\":290,\"a\":80,\"owners\":[4,36,44,76]},{\"tag\":\"mate\",\"ridge\":69,\"a\":23,\"owners\":[6,53,54,56]},{\"tag\":\"mate\",\"ridge\":69,\"a\":25,\"owners\":[5,49,52,56]},{\"tag\":\"mate\",\"ridge\":69,\"a\":52,\"owners\":[6,25,28,30,53]},{\"tag\":\"mate\",\"ridge\":69,\"a\":53,\"owners\":[5,23,28,49,52,56]},{\"tag\":\"mate\",\"ridge\":69,\"a\":54,\"owners\":[5,23,28,30,49]},{\"tag\":\"mate\",\"ridge\":73,\"a\":5,\"owners\":[7,32,34,37,57,58,59]},{\"tag\":\"mate\",\"ridge\":73,\"a\":23,\"owners\":[7,57,58,59]},{\"tag\":\"mate\",\"ridge\":73,\"a\":34,\"owners\":[5,46,52,57]},{\"tag\":\"mate\",\"ridge\":73,\"a\":52,\"owners\":[7,32,34,37,58]},{\"tag\":\"mate\",\"ridge\":73,\"a\":58,\"owners\":[5,23,32,46,52,57]},{\"tag\":\"mate\",\"ridge\":73,\"a\":59,\"owners\":[5,23,32,37,46]},{\"tag\":\"mate\",\"ridge\":76,\"a\":5,\"owners\":[15,64,67,82,83,85,86,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":15,\"owners\":[5,23,46,49,64,67,82,85]},{\"tag\":\"mate\",\"ridge\":76,\"a\":23,\"owners\":[15,82,83,85,86,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":46,\"owners\":[15,67,85,86,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":49,\"owners\":[15,64,82,83,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":83,\"owners\":[5,23,49,67,85]},{\"tag\":\"mate\",\"ridge\":76,\"a\":86,\"owners\":[5,23,46,64,82]},{\"tag\":\"mate\",\"ridge\":81,\"a\":8,\"owners\":[6,25,32,39,46,54,57,62]},{\"tag\":\"mate\",\"ridge\":81,\"a\":25,\"owners\":[8,57,61,62]},{\"tag\":\"mate\",\"ridge\":81,\"a\":42,\"owners\":[6,46,54,57,62]},{\"tag\":\"mate\",\"ridge\":81,\"a\":46,\"owners\":[8,39,42,61,62]},{\"tag\":\"mate\",\"ridge\":81,\"a\":54,\"owners\":[8,32,39,42,61]},{\"tag\":\"mate\",\"ridge\":81,\"a\":61,\"owners\":[6,25,32,46,54,57]},{\"tag\":\"mate\",\"ridge\":84,\"a\":17,\"owners\":[6,25,46,53,64,71,82,89]},{\"tag\":\"mate\",\"ridge\":84,\"a\":46,\"owners\":[17,71,89,90]},{\"tag\":\"mate\",\"ridge\":84,\"a\":53,\"owners\":[17,64,82,83,90]},{\"tag\":\"mate\",\"ridge\":84,\"a\":83,\"owners\":[6,25,53,71,89]},{\"tag\":\"mate\",\"ridge\":97,\"a\":7,\"owners\":[9,28,39,44,56,61,62]},{\"tag\":\"mate\",\"ridge\":97,\"a\":34,\"owners\":[9,56,61,62]},{\"tag\":\"mate\",\"ridge\":97,\"a\":44,\"owners\":[7,49,56,59,62]},{\"tag\":\"mate\",\"ridge\":97,\"a\":49,\"owners\":[9,39,44,61,62]},{\"tag\":\"mate\",\"ridge\":97,\"a\":59,\"owners\":[9,28,39,44,61]},{\"tag\":\"mate\",\"ridge\":97,\"a\":61,\"owners\":[7,28,34,49,56,59]},{\"tag\":\"mate\",\"ridge\":104,\"a\":34,\"owners\":[19,85,86,93,94]},{\"tag\":\"mate\",\"ridge\":104,\"a\":49,\"owners\":[19,76,93,94]},{\"tag\":\"mate\",\"ridge\":104,\"a\":58,\"owners\":[19,67,85,86,94]},{\"tag\":\"mate\",\"ridge\":104,\"a\":86,\"owners\":[7,34,58,76,93]},{\"tag\":\"mate\",\"ridge\":104,\"a\":94,\"owners\":[7,34,49,58,67,76]},{\"tag\":\"mate\",\"ridge\":321,\"a\":8,\"owners\":[9,30,37,44,58]},{\"tag\":\"mate\",\"ridge\":321,\"a\":9,\"owners\":[8,30,37,42,53]},{\"tag\":\"mate\",\"ridge\":321,\"a\":42,\"owners\":[9,58]},{\"tag\":\"mate\",\"ridge\":321,\"a\":44,\"owners\":[8,53]},{\"tag\":\"mate\",\"ridge\":321,\"a\":53,\"owners\":[9,37,44,58]},{\"tag\":\"mate\",\"ridge\":321,\"a\":58,\"owners\":[8,30,42,53]},{\"tag\":\"mate\",\"ridge\":336,\"a\":8,\"owners\":[71,79,89,95,97,99]},{\"tag\":\"mate\",\"ridge\":336,\"a\":42,\"owners\":[89,95,97,99]},{\"tag\":\"mate\",\"ridge\":336,\"a\":53,\"owners\":[79,95,97,99]},{\"tag\":\"mate\",\"ridge\":336,\"a\":61,\"owners\":[71,89,99]},{\"tag\":\"mate\",\"ridge\":336,\"a\":95,\"owners\":[8,42,53,71]},{\"tag\":\"mate\",\"ridge\":336,\"a\":97,\"owners\":[8,42,53,71,89]},{\"tag\":\"mate\",\"ridge\":336,\"a\":99,\"owners\":[8,42,53,61,71,79]},{\"tag\":\"mate\",\"ridge\":352,\"a\":9,\"owners\":[76,79,93,95,97,100]},{\"tag\":\"mate\",\"ridge\":352,\"a\":44,\"owners\":[93,95,97,100]},{\"tag\":\"mate\",\"ridge\":352,\"a\":58,\"owners\":[79,95,97,100]},{\"tag\":\"mate\",\"ridge\":352,\"a\":61,\"owners\":[76,93,100]},{\"tag\":\"mate\",\"ridge\":352,\"a\":97,\"owners\":[9,44,58,76,93]},{\"tag\":\"mate\",\"ridge\":352,\"a\":100,\"owners\":[9,44,58,61,76,79]},{\"tag\":\"mate\",\"ridge\":134,\"a\":10,\"owners\":[11,26,29,31,72,73,74]},{\"tag\":\"mate\",\"ridge\":134,\"a\":11,\"owners\":[10,24,29,31,68,70,74]},{\"tag\":\"mate\",\"ridge\":134,\"a\":24,\"owners\":[11,72,73,74]},{\"tag\":\"mate\",\"ridge\":134,\"a\":26,\"owners\":[10,68,70,74]},{\"tag\":\"mate\",\"ridge\":134,\"a\":68,\"owners\":[11,26,31,72,73]},{\"tag\":\"mate\",\"ridge\":134,\"a\":70,\"owners\":[11,26,29,31,72]},{\"tag\":\"mate\",\"ridge\":134,\"a\":72,\"owners\":[10,24,29,68,70,74]},{\"tag\":\"mate\",\"ridge\":134,\"a\":73,\"owners\":[10,24,29,31,68]},{\"tag\":\"mate\",\"ridge\":138,\"a\":24,\"owners\":[12,75,77,78]},{\"tag\":\"mate\",\"ridge\":138,\"a\":35,\"owners\":[10,65,70,75]},{\"tag\":\"mate\",\"ridge\":138,\"a\":70,\"owners\":[12,33,35,38,77]},{\"tag\":\"mate\",\"ridge\":138,\"a\":77,\"owners\":[10,24,33,65,70,75]},{\"tag\":\"mate\",\"ridge\":138,\"a\":78,\"owners\":[10,24,33,38,65]},{\"tag\":\"mate\",\"ridge\":140,\"a\":10,\"owners\":[16,47,50,82,84,85,87,88]},{\"tag\":\"mate\",\"ridge\":140,\"a\":24,\"owners\":[16,82,84,85,87,88]},{\"tag\":\"mate\",\"ridge\":140,\"a\":65,\"owners\":[16,50,85,87,88]},{\"tag\":\"mate\",\"ridge\":140,\"a\":68,\"owners\":[16,47,82,84,88]},{\"tag\":\"mate\",\"ridge\":140,\"a\":84,\"owners\":[10,24,50,68,85]},{\"tag\":\"mate\",\"ridge\":140,\"a\":87,\"owners\":[10,24,47,65,82]},{\"tag\":\"mate\",\"ridge\":140,\"a\":88,\"owners\":[10,24,47,50,65,68]},{\"tag\":\"mate\",\"ridge\":146,\"a\":11,\"owners\":[13,33,40,43,75,80,81]},{\"tag\":\"mate\",\"ridge\":146,\"a\":26,\"owners\":[13,75,80,81]},{\"tag\":\"mate\",\"ridge\":146,\"a\":43,\"owners\":[11,65,73,75,81]},{\"tag\":\"mate\",\"ridge\":146,\"a\":65,\"owners\":[13,40,43,80,81]},{\"tag\":\"mate\",\"ridge\":146,\"a\":73,\"owners\":[13,33,40,43,80]},{\"tag\":\"mate\",\"ridge\":146,\"a\":80,\"owners\":[11,26,33,65,73,75]},{\"tag\":\"mate\",\"ridge\":148,\"a\":26,\"owners\":[18,82,84,89,90]},{\"tag\":\"mate\",\"ridge\":148,\"a\":65,\"owners\":[18,55,89,90]},{\"tag\":\"mate\",\"ridge\":148,\"a\":72,\"owners\":[18,47,82,84,90]},{\"tag\":\"mate\",\"ridge\":148,\"a\":84,\"owners\":[11,26,55,72,89]},{\"tag\":\"mate\",\"ridge\":148,\"a\":90,\"owners\":[11,26,47,55,65,72]},{\"tag\":\"mate\",\"ridge\":162,\"a\":35,\"owners\":[14,74,80,81]},{\"tag\":\"mate\",\"ridge\":162,\"a\":45,\"owners\":[12,68,74,78,81]},{\"tag\":\"mate\",\"ridge\":162,\"a\":68,\"owners\":[14,40,45,80,81]},{\"tag\":\"mate\",\"ridge\":162,\"a\":78,\"owners\":[14,29,40,45,80]},{\"tag\":\"mate\",\"ridge\":162,\"a\":80,\"owners\":[12,29,35,68,74,78]},{\"tag\":\"mate\",\"ridge\":168,\"a\":12,\"owners\":[20,50,60,85,87,93,94]},{\"tag\":\"mate\",\"ridge\":168,\"a\":20,\"owners\":[12,35,50,60,68,77,85,93]},{\"tag\":\"mate\",\"ridge\":168,\"a\":35,\"owners\":[20,85,87,93,94]},{\"tag\":\"mate\",\"ridge\":168,\"a\":68,\"owners\":[20,60,93,94]},{\"tag\":\"mate\",\"ridge\":168,\"a\":77,\"owners\":[20,50,85,87,94]},{\"tag\":\"mate\",\"ridge\":168,\"a\":87,\"owners\":[12,35,60,77,93]},{\"tag\":\"mate\",\"ridge\":168,\"a\":94,\"owners\":[12,35,50,60,68,77]},{\"tag\":\"mate\",\"ridge\":386,\"a\":13,\"owners\":[14,31,38,45,77]},{\"tag\":\"mate\",\"ridge\":386,\"a\":43,\"owners\":[14,77]},{\"tag\":\"mate\",\"ridge\":386,\"a\":45,\"owners\":[13,72]},{\"tag\":\"mate\",\"ridge\":386,\"a\":72,\"owners\":[14,38,45,77]},{\"tag\":\"mate\",\"ridge\":386,\"a\":77,\"owners\":[13,31,43,72]},{\"tag\":\"mate\",\"ridge\":400,\"a\":13,\"owners\":[55,63,89,95,98,99]},{\"tag\":\"mate\",\"ridge\":400,\"a\":43,\"owners\":[89,95,98,99]},{\"tag\":\"mate\",\"ridge\":400,\"a\":72,\"owners\":[63,95,98,99]},{\"tag\":\"mate\",\"ridge\":400,\"a\":80,\"owners\":[55,89,99]},{\"tag\":\"mate\",\"ridge\":400,\"a\":95,\"owners\":[13,43,55,72]},{\"tag\":\"mate\",\"ridge\":400,\"a\":98,\"owners\":[13,43,55,72,89]},{\"tag\":\"mate\",\"ridge\":400,\"a\":99,\"owners\":[13,43,55,63,72,80]},{\"tag\":\"mate\",\"ridge\":416,\"a\":14,\"owners\":[60,63,93,95,98,100]},{\"tag\":\"mate\",\"ridge\":416,\"a\":45,\"owners\":[93,95,98,100]},{\"tag\":\"mate\",\"ridge\":416,\"a\":77,\"owners\":[63,95,98,100]},{\"tag\":\"mate\",\"ridge\":416,\"a\":80,\"owners\":[60,93,100]},{\"tag\":\"mate\",\"ridge\":416,\"a\":95,\"owners\":[14,45,60,77]},{\"tag\":\"mate\",\"ridge\":416,\"a\":98,\"owners\":[14,45,60,77,93]},{\"tag\":\"mate\",\"ridge\":416,\"a\":100,\"owners\":[14,45,60,63,77,80]},{\"tag\":\"mate\",\"ridge\":524,\"a\":16,\"owners\":[15,48,51,52,66,69,83,86]},{\"tag\":\"mate\",\"ridge\":524,\"a\":52,\"owners\":[16,66,69,70,84,87]},{\"tag\":\"mate\",\"ridge\":524,\"a\":70,\"owners\":[15,48,51,52,83,86]},{\"tag\":\"mate\",\"ridge\":524,\"a\":83,\"owners\":[16,51,69,70,87]},{\"tag\":\"mate\",\"ridge\":524,\"a\":84,\"owners\":[15,51,52,69,86]},{\"tag\":\"mate\",\"ridge\":524,\"a\":86,\"owners\":[16,48,66,70,84]},{\"tag\":\"mate\",\"ridge\":524,\"a\":87,\"owners\":[15,48,52,66,83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":15,\"owners\":[17,54,56,90,91]},{\"tag\":\"mate\",\"ridge\":580,\"a\":17,\"owners\":[15,52,56,86,88,91]},{\"tag\":\"mate\",\"ridge\":580,\"a\":52,\"owners\":[17,90,91]},{\"tag\":\"mate\",\"ridge\":580,\"a\":54,\"owners\":[15,86,88,91]},{\"tag\":\"mate\",\"ridge\":580,\"a\":88,\"owners\":[17,54,56]},{\"tag\":\"mate\",\"ridge\":580,\"a\":90,\"owners\":[15,52,56,86]},{\"tag\":\"mate\",\"ridge\":584,\"a\":19,\"owners\":[15,52,57,83,88,92]},{\"tag\":\"mate\",\"ridge\":584,\"a\":52,\"owners\":[19,92,94]},{\"tag\":\"mate\",\"ridge\":584,\"a\":59,\"owners\":[15,83,88,92]},{\"tag\":\"mate\",\"ridge\":584,\"a\":83,\"owners\":[19,59,94]},{\"tag\":\"mate\",\"ridge\":584,\"a\":88,\"owners\":[19,57,59]},{\"tag\":\"mate\",\"ridge\":584,\"a\":94,\"owners\":[15,52,57,83]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[16,70,74,87,88,91]},{\"tag\":\"mate\",\"ridge\":644,\"a\":70,\"owners\":[18,90,91]},{\"tag\":\"mate\",\"ridge\":644,\"a\":73,\"owners\":[16,87,88,91]},{\"tag\":\"mate\",\"ridge\":644,\"a\":87,\"owners\":[18,73,90]},{\"tag\":\"mate\",\"ridge\":644,\"a\":88,\"owners\":[18,73,74]},{\"tag\":\"mate\",\"ridge\":644,\"a\":90,\"owners\":[16,70,74,87]},{\"tag\":\"mate\",\"ridge\":648,\"a\":20,\"owners\":[16,70,75,84,88,92]},{\"tag\":\"mate\",\"ridge\":648,\"a\":70,\"owners\":[20,92,94]},{\"tag\":\"mate\",\"ridge\":648,\"a\":78,\"owners\":[16,84,88,92]},{\"tag\":\"mate\",\"ridge\":648,\"a\":84,\"owners\":[20,78,94]},{\"tag\":\"mate\",\"ridge\":648,\"a\":88,\"owners\":[20,75,78]},{\"tag\":\"mate\",\"ridge\":648,\"a\":94,\"owners\":[16,70,75,84]},{\"tag\":\"mate\",\"ridge\":532,\"a\":17,\"owners\":[18,48,66,73,84]},{\"tag\":\"mate\",\"ridge\":532,\"a\":54,\"owners\":[18,66,73,84]},{\"tag\":\"mate\",\"ridge\":532,\"a\":73,\"owners\":[17,48,54,83]},{\"tag\":\"mate\",\"ridge\":532,\"a\":83,\"owners\":[18,73]},{\"tag\":\"mate\",\"ridge\":532,\"a\":84,\"owners\":[17,54]},{\"tag\":\"mate\",\"ridge\":592,\"a\":17,\"owners\":[57,62,92,96,97,99]},{\"tag\":\"mate\",\"ridge\":592,\"a\":54,\"owners\":[92,96,97,99]},{\"tag\":\"mate\",\"ridge\":592,\"a\":83,\"owners\":[62,96,97,99]},{\"tag\":\"mate\",\"ridge\":592,\"a\":90,\"owners\":[57,62,97]},{\"tag\":\"mate\",\"ridge\":592,\"a\":96,\"owners\":[17,54,57,83]},{\"tag\":\"mate\",\"ridge\":592,\"a\":99,\"owners\":[17,54,57,62,83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":18,\"owners\":[75,81,92,96,98,99]},{\"tag\":\"mate\",\"ridge\":656,\"a\":73,\"owners\":[92,96,98,99]},{\"tag\":\"mate\",\"ridge\":656,\"a\":84,\"owners\":[81,96,98,99]},{\"tag\":\"mate\",\"ridge\":656,\"a\":90,\"owners\":[75,81,98]},{\"tag\":\"mate\",\"ridge\":656,\"a\":96,\"owners\":[18,73,75,84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":98,\"owners\":[18,73,75,84,90,92]},{\"tag\":\"mate\",\"ridge\":656,\"a\":99,\"owners\":[18,73,75,81,84]},{\"tag\":\"mate\",\"ridge\":552,\"a\":19,\"owners\":[20,51,69,78,87]},{\"tag\":\"mate\",\"ridge\":552,\"a\":59,\"owners\":[20,69,78,87]},{\"tag\":\"mate\",\"ridge\":552,\"a\":78,\"owners\":[19,51,59,86]},{\"tag\":\"mate\",\"ridge\":552,\"a\":86,\"owners\":[20,78]},{\"tag\":\"mate\",\"ridge\":552,\"a\":87,\"owners\":[19,59]},{\"tag\":\"mate\",\"ridge\":608,\"a\":19,\"owners\":[56,62,91,96,97,100]},{\"tag\":\"mate\",\"ridge\":608,\"a\":59,\"owners\":[91,96,97,100]},{\"tag\":\"mate\",\"ridge\":608,\"a\":86,\"owners\":[62,96,97,100]},{\"tag\":\"mate\",\"ridge\":608,\"a\":94,\"owners\":[56,62,97]},{\"tag\":\"mate\",\"ridge\":608,\"a\":96,\"owners\":[19,56,59,86]},{\"tag\":\"mate\",\"ridge\":608,\"a\":97,\"owners\":[19,56,59,86,91,94]},{\"tag\":\"mate\",\"ridge\":608,\"a\":100,\"owners\":[19,56,59,62,86]},{\"tag\":\"mate\",\"ridge\":672,\"a\":20,\"owners\":[74,81,91,96,98,100]},{\"tag\":\"mate\",\"ridge\":672,\"a\":78,\"owners\":[91,96,98,100]},{\"tag\":\"mate\",\"ridge\":672,\"a\":87,\"owners\":[81,96,98,100]},{\"tag\":\"mate\",\"ridge\":672,\"a\":94,\"owners\":[74,81,98]},{\"tag\":\"mate\",\"ridge\":672,\"a\":96,\"owners\":[20,74,78,87]},{\"tag\":\"mate\",\"ridge\":672,\"a\":98,\"owners\":[20,74,78,87,91,94]},{\"tag\":\"mate\",\"ridge\":672,\"a\":100,\"owners\":[20,74,78,81,87]},{\"tag\":\"mate\",\"ridge\":102,\"a\":28,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":102,\"a\":67,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":165,\"a\":29,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":165,\"a\":50,\"owners\":[29]},{\"tag\":\"mate\",\"ridge\":326,\"a\":30,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":326,\"a\":71,\"owners\":[30]},{\"tag\":\"mate\",\"ridge\":389,\"a\":31,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":389,\"a\":55,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":90,\"a\":32,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":90,\"a\":64,\"owners\":[32]},{\"tag\":\"mate\",\"ridge\":153,\"a\":33,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":153,\"a\":47,\"owners\":[33]},{\"tag\":\"mate\",\"ridge\":330,\"a\":37,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":330,\"a\":76,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":393,\"a\":38,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":393,\"a\":60,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":114,\"a\":39,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":114,\"a\":79,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":177,\"a\":40,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":177,\"a\":63,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":537,\"a\":48,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":537,\"a\":57,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":549,\"a\":51,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":549,\"a\":56,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":561,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":538,\"a\":66,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":538,\"a\":75,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":550,\"a\":69,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":550,\"a\":74,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":562,\"a\":81,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":216,\"a\":82,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":216,\"a\":92,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":228,\"a\":85,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":228,\"a\":91,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":452,\"a\":89,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":93,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":97,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":816,\"a\":98,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":960,\"a\":99,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":960,\"a\":100,\"owners\":[99]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,102]},{\"tag\":\"group_take\",\"kind\":1,\"index\":1,\"member\":1,\"full_literals\":[-2,103]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-3,104]},{\"tag\":\"group_take\",\"kind\":1,\"index\":3,\"member\":3,\"full_literals\":[-4,105]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-5,106]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-6,107]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-7,108]},{\"tag\":\"group_or\",\"kind\":1,\"index\":7,\"members\":[7],\"full_literals\":[-109,8]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-8,109]},{\"tag\":\"group_or\",\"kind\":1,\"index\":8,\"members\":[8],\"full_literals\":[-110,9]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-9,110]},{\"tag\":\"group_or\",\"kind\":1,\"index\":9,\"members\":[9],\"full_literals\":[-111,10]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-10,111]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-11,112]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-12,113]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-13,114]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-14,115]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-15,116]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-16,117]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-17,118]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-18,119]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-19,120]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-20,121]},{\"tag\":\"group_take\",\"kind\":1,\"index\":20,\"member\":20,\"full_literals\":[-21,122]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-105,-106,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-124,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-125,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-104,-124,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-126,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-127,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-123,false,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-123,-126,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-108,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-107,false,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-107,-108,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-132,110,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-111,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-111,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-134,109,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-132,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-133,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-109,false,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-109,-132,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-109,-133,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-134,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-135,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-136,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-130,false,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-130,-134,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-130,-135,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-130,-136,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-131,false,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-131,-134,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-137,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-139,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-128,false,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-128,-137,142],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-128,-138,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-128,-139,144],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-128,-140,145],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-129,false,142],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-129,-137,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-129,-139,145],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-112,false,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-112,-113,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-116,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-115,false,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-115,-116,149],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-148,150],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-149,151],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-114,false,150],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-114,-148,151],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-114,-149,152],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-150,153],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-151,154],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-146,false,153],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-146,-150,154],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-146,-151,155],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-146,-152,156],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-147,false,154],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-147,-150,155],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-119,157],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-118,false,157],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-118,-119,158],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16,17],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0031\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-157,159],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16,17],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0031\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-158,160],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16,17],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-117,false,159],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16,17],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-117,-157,160],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0039\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-122,161],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-121,false,161],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-121,-122,162],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19,20],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-161,163],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19,20],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-162,164],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19,20],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-120,false,163],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19,20],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-120,-161,164],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19,20],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-120,-162,165],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-163,166],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-164,167],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-159,false,166],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-159,-163,167],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-159,-164,168],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-159,-165,169],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-160,false,167],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-160,-163,168],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-160,-164,169],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-168,172],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":4,\"direction\":\"forward\",\"full_literals\":[false,-169,173],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-153,false,170],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-153,-166,171],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-153,-167,172],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-153,-168,173],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-153,-169,174],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-154,false,171],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-154,-166,172],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-154,-167,173],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-154,-168,174],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-154,-169,175],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-155,false,172],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-155,-166,173],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-155,-167,174],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-155,-168,175],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":4,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-156,false,173],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19,20],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":6,\"direction\":\"forward\",\"full_literals\":[false,-175,176],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19,20],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":5,\"direction\":\"forward\",\"full_literals\":[-141,-174,176],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19,20],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-142,-173,176],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19,20],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-143,-172,176],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19,20],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":4,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-144,-171,176],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19,20],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":5,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-145,-170,176],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":5,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[41,61,80],\"full_literals\":[-177,42,62,81]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":41,\"full_literals\":[-42,177]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":61,\"full_literals\":[-62,177]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":80,\"full_literals\":[-81,177]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[88,90,94],\"full_literals\":[-178,89,91,95]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":88,\"full_literals\":[-89,178]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":90,\"full_literals\":[-91,178]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":94,\"full_literals\":[-95,178]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[52,54,59],\"full_literals\":[-179,53,55,60]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":52,\"full_literals\":[-53,179]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":54,\"full_literals\":[-55,179]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":59,\"full_literals\":[-60,179]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[27,53,72],\"full_literals\":[-180,28,54,73]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":27,\"full_literals\":[-28,180]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":53,\"full_literals\":[-54,180]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":72,\"full_literals\":[-73,180]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[36,58,77],\"full_literals\":[-181,37,59,78]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":36,\"full_literals\":[-37,181]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":58,\"full_literals\":[-59,181]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":77,\"full_literals\":[-78,181]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[70,73,78],\"full_literals\":[-182,71,74,79]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":70,\"full_literals\":[-71,182]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":73,\"full_literals\":[-74,182]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":78,\"full_literals\":[-79,182]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[21,46,65,83,84],\"full_literals\":[-183,22,47,66,84,85]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":21,\"full_literals\":[-22,183]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":46,\"full_literals\":[-47,183]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":83,\"full_literals\":[-84,183]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":84,\"full_literals\":[-85,183]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[24,26,35,43,45],\"full_literals\":[-184,25,27,36,44,46]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":24,\"full_literals\":[-25,184]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":26,\"full_literals\":[-27,184]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":35,\"full_literals\":[-36,184]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":43,\"full_literals\":[-44,184]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":45,\"full_literals\":[-46,184]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[23,25,34,42,44],\"full_literals\":[-185,24,26,35,43,45]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":23,\"full_literals\":[-24,185]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":25,\"full_literals\":[-26,185]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":34,\"full_literals\":[-35,185]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":42,\"full_literals\":[-43,185]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":44,\"full_literals\":[-45,185]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[22,49,68,86,87],\"full_literals\":[-186,23,50,69,87,88]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":22,\"full_literals\":[-23,186]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":68,\"full_literals\":[-69,186]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":87,\"full_literals\":[-88,186]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-187,177,178],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-178,187],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-188,177,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-177,false,187],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-188,false,178],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-177,-178,188],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-189,180,181],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-190,180,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-190,false,181],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-180,-181,190],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-191,179,190],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-192,179,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-191,false,189],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-192,false,190],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-179,-190,192],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-193,187,192],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-194,187,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-193,188,191],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-194,188,192],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-187,-192,194],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-195,188,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-194,false,191],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-195,false,192],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-196,182,183],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-197,182,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-197,false,183],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-182,-183,197],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-198,185,186],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-199,185,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-199,false,186],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-200,184,199],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-201,184,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-200,false,198],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-201,false,199],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-184,-199,201],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-202,196,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-202,197,201],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-203,197,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-202,false,200],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-203,false,201],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-197,-201,203],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-204,193,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-204,194,203],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-204,195,202],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"forward\",\"full_literals\":[-194,-203,205],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[95,97,99],\"full_literals\":[-206,96,98,100]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":95,\"full_literals\":[-96,206]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":97,\"full_literals\":[-98,206]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":99,\"full_literals\":[-100,206]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[96,98,100],\"full_literals\":[-207,97,99,101]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":96,\"full_literals\":[-97,207]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":98,\"full_literals\":[-99,207]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":100,\"full_literals\":[-101,207]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[28,30,32,37,39],\"full_literals\":[-208,29,31,33,38,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":28,\"full_literals\":[-29,208]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":30,\"full_literals\":[-31,208]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":32,\"full_literals\":[-33,208]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":37,\"full_literals\":[-38,208]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":39,\"full_literals\":[-40,208]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[29,31,33,38,40],\"full_literals\":[-209,30,32,34,39,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":29,\"full_literals\":[-30,209]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":31,\"full_literals\":[-32,209]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":33,\"full_literals\":[-34,209]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":38,\"full_literals\":[-39,209]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-41,209]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[48,51,62],\"full_literals\":[-210,49,52,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":48,\"full_literals\":[-49,210]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":51,\"full_literals\":[-52,210]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[47,57,64,66,82],\"full_literals\":[-211,48,58,65,67,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-48,211]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":57,\"full_literals\":[-58,211]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":64,\"full_literals\":[-65,211]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-67,211]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-83,211]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[50,55,60,63],\"full_literals\":[-212,51,56,61,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":50,\"full_literals\":[-51,212]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":55,\"full_literals\":[-56,212]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":60,\"full_literals\":[-61,212]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-64,212]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[69,75,81],\"full_literals\":[-213,70,76,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":69,\"full_literals\":[-70,213]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-76,213]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[67,71,76,79],\"full_literals\":[-214,68,72,77,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":67,\"full_literals\":[-68,214]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":71,\"full_literals\":[-72,214]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":76,\"full_literals\":[-77,214]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":79,\"full_literals\":[-80,214]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[56,74,85],\"full_literals\":[-215,57,75,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":56,\"full_literals\":[-57,215]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":74,\"full_literals\":[-75,215]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":85,\"full_literals\":[-86,215]},{\"tag\":\"group_or\",\"kind\":3,\"index\":10,\"members\":[89,91,92,93],\"full_literals\":[-216,90,92,93,94]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":91,\"full_literals\":[-92,216]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":92,\"full_literals\":[-93,216]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-207,217],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-218,206,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-206,false,217],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-218,false,207],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-219,209,210],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-210,219],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-209,false,219],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-220,208,219],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-219,220],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0066\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-208,false,220],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-220,221],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-217,false,221],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-222,218,220],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-217,-220,222],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0074\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-223,212,213],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0074\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-213,223],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0074\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-212,false,223],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"grouped3_0071\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-224,211,223],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"grouped3_0071\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-223,224],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"grouped3_0071\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-211,false,224],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"grouped3_0071\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-211,-223,225],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"grouped3_0079\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-226,215,216],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"grouped3_0079\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-216,226],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"grouped3_0079\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-215,false,226],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"grouped3_0079\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-215,-216,227],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0077\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-228,214,226],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0077\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-226,228],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0077\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-227,229],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0077\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-214,false,228],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-230,224,228],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-228,230],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-229,231],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-224,false,230],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-224,-228,231],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0072\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-225,false,231],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-232,222,230],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-221,-231,233],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-222,-230,233],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[3,7,13,17,18,22,26,44,52,53,70,77,94,97,98]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[1,6,12,17,18,22,42,45,52,58,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[1,5,8,9,20,24,34,41,54,72,77,84,86,99,100]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[1,9,14,17,18,23,36,43,53,59,65,78,88,97,98]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[1,7,16,17,18,22,43,44,52,53,65,77,94,97,98]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[1,5,8,9,14,24,34,41,54,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[1,6,12,19,20,22,42,45,52,58,70,72,90,97,98]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[1,7,16,19,20,22,43,44,52,53,65,77,90,97,98]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[3,7,13,19,20,22,26,44,52,53,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[3,8,14,15,18,21,35,44,49,54,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[1,9,14,15,19,24,36,42,49,54,72,78,84,95,96]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[1,5,7,9,14,24,36,42,54,72,78,84,86,95,96]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[1,3,4,5,20,24,34,54,61,72,77,84,86,99,100]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[1,4,9,15,20,22,42,46,59,70,72,77,90,97,98]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[1,7,14,16,19,22,43,44,52,53,65,78,90,97,98]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[1,2,3,8,15,24,44,49,54,72,77,84,94,97,98]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[1,2,3,8,15,24,44,46,59,72,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[1,7,9,14,16,23,36,43,53,68,73,83,94,97,98]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[1,7,9,14,16,23,36,43,53,65,78,86,90,97,98]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[1,7,9,14,16,24,36,42,46,72,78,86,90,97,98]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[1,9,14,15,16,23,36,43,53,59,65,78,90,97,98]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[1,5,7,9,14,24,36,42,54,72,78,84,86,97,98]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[1,9,14,15,19,24,36,42,49,54,72,78,84,97,98]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[1,9,14,17,20,23,36,43,53,59,68,73,88,97,98]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[1,9,14,15,19,24,36,42,49,54,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[1,5,7,9,14,24,36,42,54,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[1,5,9,13,19,24,34,41,53,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[1,8,14,18,20,23,35,41,54,58,70,72,86,99,100]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[1,3,8,15,20,22,44,46,59,70,72,77,90,97,98]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[1,6,13,16,19,22,42,45,52,58,65,78,90,97,98]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[3,8,13,15,20,22,26,44,46,59,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[3,7,14,17,19,24,25,36,52,61,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":32,\"vertices\":[1,7,14,16,18,23,36,43,54,61,65,78,86,99,100]},{\"tag\":\"block\",\"leaf\":33,\"vertices\":[1,5,6,9,12,24,36,42,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":34,\"vertices\":[1,6,14,16,20,23,36,43,59,61,68,73,83,99,100]},{\"tag\":\"block\",\"leaf\":35,\"vertices\":[1,5,7,9,11,24,36,42,54,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":36,\"vertices\":[0,1,4,9,19,34,43,52,53,65,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":37,\"vertices\":[0,1,2,6,17,42,45,52,58,68,72,84,94,97,98]},{\"tag\":\"block\",\"leaf\":38,\"vertices\":[1,2,3,5,13,24,44,53,59,73,77,83,87,95,96]},{\"tag\":\"block\",\"leaf\":39,\"vertices\":[1,2,3,5,13,24,44,53,59,73,77,83,87,97,98]},{\"tag\":\"block\",\"leaf\":40,\"vertices\":[1,2,3,8,15,23,45,54,58,68,72,84,94,97,98]},{\"tag\":\"block\",\"leaf\":41,\"vertices\":[1,3,9,16,20,23,36,53,59,68,73,80,83,99,100]},{\"tag\":\"block\",\"leaf\":42,\"vertices\":[1,3,5,9,12,24,36,53,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":43,\"vertices\":[1,2,5,8,14,24,41,54,58,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":44,\"vertices\":[1,2,3,5,13,24,44,53,59,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":45,\"vertices\":[1,3,4,5,14,24,34,54,61,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":46,\"vertices\":[1,3,5,7,14,24,36,54,61,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":47,\"vertices\":[0,1,2,5,10,42,45,54,58,72,78,84,86,95,96]},{\"tag\":\"block\",\"leaf\":48,\"vertices\":[0,1,2,5,10,42,45,54,58,72,78,84,86,97,98]},{\"tag\":\"block\",\"leaf\":49,\"vertices\":[0,1,2,5,15,42,45,54,58,68,72,84,94,97,98]},{\"tag\":\"block\",\"leaf\":50,\"vertices\":[1,2,3,5,12,24,44,53,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":51,\"vertices\":[4,6,14,19,20,21,35,42,52,58,70,72,90,97,98]},{\"tag\":\"block\",\"leaf\":52,\"vertices\":[3,8,12,17,18,22,25,45,52,58,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":53,\"vertices\":[4,9,11,19,20,21,34,43,52,53,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":54,\"vertices\":[8,9,11,15,19,24,27,36,49,54,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":55,\"vertices\":[8,9,12,15,17,24,27,36,46,59,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":56,\"vertices\":[6,13,14,16,20,23,27,36,59,61,68,73,83,99,100]},{\"tag\":\"block\",\"leaf\":57,\"vertices\":[7,13,14,16,18,23,27,36,54,61,65,78,86,99,100]},{\"tag\":\"block\",\"leaf\":58,\"vertices\":[2,7,11,19,20,21,43,44,52,53,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":59,\"vertices\":[1,7,11,17,18,22,43,44,52,53,70,77,94,97,98]},{\"tag\":\"block\",\"leaf\":60,\"vertices\":[2,6,12,19,20,21,42,45,52,58,70,72,90,97,98]},{\"tag\":\"block\",\"leaf\":61,\"vertices\":[5,6,8,9,12,24,27,36,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":62,\"vertices\":[5,7,8,9,11,24,27,36,54,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":63,\"vertices\":[7,10,11,13,14,23,27,36,54,61,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":64,\"vertices\":[6,10,12,13,14,23,27,36,59,61,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":65,\"vertices\":[2,5,8,9,18,24,25,41,59,72,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":66,\"vertices\":[1,10,13,14,19,23,35,41,53,58,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":67,\"vertices\":[2,10,13,14,17,23,26,41,53,58,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":68,\"vertices\":[1,5,14,17,18,22,43,44,53,59,65,78,88,97,98]},{\"tag\":\"block\",\"leaf\":69,\"vertices\":[2,5,13,19,20,21,42,45,54,58,68,73,88,97,98]},{\"tag\":\"block\",\"leaf\":70,\"vertices\":[1,9,10,17,18,22,42,45,46,59,72,78,88,97,98]},{\"tag\":\"block\",\"leaf\":71,\"vertices\":[2,8,10,19,20,21,43,44,49,54,73,77,88,97,98]},{\"tag\":\"block\",\"leaf\":72,\"vertices\":[2,8,13,19,20,23,27,45,54,58,68,73,88,97,98]},{\"tag\":\"block\",\"leaf\":73,\"vertices\":[1,9,14,17,18,24,36,42,46,59,72,78,88,97,98]},{\"tag\":\"block\",\"leaf\":74,\"vertices\":[2,8,13,19,20,24,27,44,49,54,73,77,88,97,98]},{\"tag\":\"block\",\"leaf\":75,\"vertices\":[5,8,9,18,20,21,34,41,54,70,72,77,86,99,100]},{\"tag\":\"block\",\"leaf\":76,\"vertices\":[5,8,9,18,20,22,25,41,59,70,72,77,83,99,100]},{\"tag\":\"block\",\"leaf\":77,\"vertices\":[10,13,14,17,19,21,35,41,52,53,58,73,87,99,100]},{\"tag\":\"block\",\"leaf\":78,\"vertices\":[10,13,14,17,19,22,26,41,52,53,58,78,84,99,100]},{\"tag\":\"block\",\"leaf\":79,\"vertices\":[2,6,16,19,20,21,42,45,52,58,68,72,90,97,98]},{\"tag\":\"block\",\"leaf\":80,\"vertices\":[1,12,15,17,18,22,42,45,46,58,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":81,\"vertices\":[2,11,15,19,20,21,43,44,49,53,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":82,\"vertices\":[4,5,8,9,11,24,27,34,54,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":83,\"vertices\":[3,5,8,9,12,24,25,36,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":84,\"vertices\":[4,6,10,13,14,23,27,35,59,61,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":85,\"vertices\":[3,7,10,13,14,23,26,36,54,61,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":86,\"vertices\":[2,5,8,9,13,24,25,41,59,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":87,\"vertices\":[1,9,10,13,14,23,35,41,53,59,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":88,\"vertices\":[2,8,10,13,14,23,26,41,54,58,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":89,\"vertices\":[1,5,17,18,20,22,43,44,53,59,65,77,88,97,98]},{\"tag\":\"block\",\"leaf\":90,\"vertices\":[2,5,18,19,20,21,42,45,54,58,68,72,88,97,98]},{\"tag\":\"block\",\"leaf\":91,\"vertices\":[1,10,17,18,19,22,42,45,46,58,72,78,88,97,98]},{\"tag\":\"block\",\"leaf\":92,\"vertices\":[2,10,17,19,20,21,43,44,49,53,73,77,88,97,98]},{\"tag\":\"block\",\"leaf\":93,\"vertices\":[2,7,11,17,18,21,43,44,52,53,70,77,94,97,98]},{\"tag\":\"block\",\"leaf\":94,\"vertices\":[1,7,11,19,20,22,43,44,52,53,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":95,\"vertices\":[2,6,12,17,18,21,42,45,52,58,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":96,\"vertices\":[5,6,12,13,14,24,27,36,59,61,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":97,\"vertices\":[5,7,11,13,14,24,27,36,54,61,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":98,\"vertices\":[7,8,9,10,11,23,27,36,54,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":99,\"vertices\":[6,8,9,10,12,23,27,36,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":100,\"vertices\":[2,6,16,17,18,21,42,45,52,58,68,72,94,97,98]},{\"tag\":\"block\",\"leaf\":101,\"vertices\":[1,12,15,19,20,22,42,45,46,58,70,72,90,97,98]},{\"tag\":\"block\",\"leaf\":102,\"vertices\":[2,11,15,17,18,21,43,44,49,53,70,77,94,97,98]},{\"tag\":\"block\",\"leaf\":103,\"vertices\":[4,5,11,13,14,24,27,34,54,61,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":104,\"vertices\":[3,5,12,13,14,24,25,36,59,61,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":105,\"vertices\":[4,6,8,9,10,23,27,35,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":106,\"vertices\":[3,7,8,9,10,23,26,36,54,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":107,\"vertices\":[4,6,14,17,18,21,35,42,52,58,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":108,\"vertices\":[3,8,12,19,20,22,25,45,52,58,70,72,90,97,98]},{\"tag\":\"block\",\"leaf\":109,\"vertices\":[4,9,11,17,18,21,34,43,52,53,70,77,94,97,98]},{\"tag\":\"block\",\"leaf\":110,\"vertices\":[11,13,14,15,19,24,27,36,49,54,61,78,84,99,100]},{\"tag\":\"block\",\"leaf\":111,\"vertices\":[12,13,14,15,17,24,27,36,46,59,61,73,87,99,100]},{\"tag\":\"block\",\"leaf\":112,\"vertices\":[6,8,9,16,20,23,27,36,59,68,73,80,83,99,100]},{\"tag\":\"block\",\"leaf\":113,\"vertices\":[7,8,9,16,18,23,27,36,54,65,78,80,86,99,100]},{\"tag\":\"block\",\"leaf\":114,\"vertices\":[4,9,13,15,20,22,26,42,46,59,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":115,\"vertices\":[3,9,13,16,17,21,34,45,52,53,68,73,94,97,98]},{\"tag\":\"block\",\"leaf\":116,\"vertices\":[4,8,14,16,19,22,25,43,52,58,65,78,90,97,98]},{\"tag\":\"block\",\"leaf\":117,\"vertices\":[3,9,15,17,20,23,26,36,53,59,68,80,84,99,100]},{\"tag\":\"block\",\"leaf\":118,\"vertices\":[4,8,15,18,19,23,27,35,54,58,65,80,87,99,100]},{\"tag\":\"block\",\"leaf\":119,\"vertices\":[3,14,16,18,19,24,25,36,49,61,72,78,83,99,100]},{\"tag\":\"block\",\"leaf\":120,\"vertices\":[4,13,16,17,20,24,27,34,46,61,73,77,86,99,100]},{\"tag\":\"block\",\"leaf\":121,\"vertices\":[2,8,13,15,17,24,27,44,46,59,73,77,87,95,96]},{\"tag\":\"block\",\"leaf\":122,\"vertices\":[1,9,14,16,20,23,36,43,53,59,68,73,83,95,96]},{\"tag\":\"block\",\"leaf\":123,\"vertices\":[2,8,13,16,18,23,27,45,54,58,65,78,86,95,96]},{\"tag\":\"block\",\"leaf\":124,\"vertices\":[3,5,13,18,20,22,26,44,53,59,70,77,83,95,96]},{\"tag\":\"block\",\"leaf\":125,\"vertices\":[4,5,14,18,20,21,35,42,54,58,70,72,86,95,96]},{\"tag\":\"block\",\"leaf\":126,\"vertices\":[3,8,10,17,19,22,25,45,52,58,72,78,84,95,96]},{\"tag\":\"block\",\"leaf\":127,\"vertices\":[4,9,10,17,19,21,34,43,52,53,73,77,87,95,96]},{\"tag\":\"block\",\"leaf\":128,\"vertices\":[2,5,6,8,13,24,27,44,59,73,77,83,87,95,96]},{\"tag\":\"block\",\"leaf\":129,\"vertices\":[1,9,10,12,14,23,36,43,53,59,73,83,87,95,96]},{\"tag\":\"block\",\"leaf\":130,\"vertices\":[2,8,10,11,13,23,27,45,54,58,78,84,86,95,96]},{\"tag\":\"block\",\"leaf\":131,\"vertices\":[1,5,11,18,20,22,43,44,53,59,70,77,83,95,96]},{\"tag\":\"block\",\"leaf\":132,\"vertices\":[2,5,12,18,20,21,42,45,54,58,70,72,86,95,96]},{\"tag\":\"block\",\"leaf\":133,\"vertices\":[1,6,10,17,19,22,42,45,52,58,72,78,84,95,96]},{\"tag\":\"block\",\"leaf\":134,\"vertices\":[2,7,10,17,19,21,43,44,52,53,73,77,87,95,96]},{\"tag\":\"block\",\"leaf\":135,\"vertices\":[2,3,4,5,18,24,25,59,61,72,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":136,\"vertices\":[1,3,4,10,19,23,35,53,58,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":137,\"vertices\":[2,3,4,10,17,23,26,53,58,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":138,\"vertices\":[1,5,14,15,16,22,43,44,53,59,65,78,90,97,98]},{\"tag\":\"block\",\"leaf\":139,\"vertices\":[2,5,13,15,16,21,42,45,54,58,68,73,94,97,98]},{\"tag\":\"block\",\"leaf\":140,\"vertices\":[1,9,10,15,16,22,42,45,46,59,72,78,90,97,98]},{\"tag\":\"block\",\"leaf\":141,\"vertices\":[2,8,10,15,16,21,43,44,49,54,73,77,94,97,98]},{\"tag\":\"block\",\"leaf\":142,\"vertices\":[2,3,8,15,18,21,44,49,54,70,72,77,94,97,98]},{\"tag\":\"block\",\"leaf\":143,\"vertices\":[1,4,14,16,19,22,43,52,53,58,65,78,90,97,98]},{\"tag\":\"block\",\"leaf\":144,\"vertices\":[2,3,13,16,17,21,45,52,53,58,68,73,94,97,98]},{\"tag\":\"block\",\"leaf\":145,\"vertices\":[3,5,14,16,18,24,25,36,59,61,72,78,83,99,100]},{\"tag\":\"block\",\"leaf\":146,\"vertices\":[4,5,13,16,20,24,27,34,54,61,73,77,86,99,100]},{\"tag\":\"block\",\"leaf\":147,\"vertices\":[3,9,10,15,17,23,26,36,53,59,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":148,\"vertices\":[4,8,10,15,19,23,27,35,54,58,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":149,\"vertices\":[2,6,13,16,17,21,42,45,52,58,68,73,94,97,98]},{\"tag\":\"block\",\"leaf\":150,\"vertices\":[1,9,12,15,20,22,42,45,46,59,70,72,90,97,98]},{\"tag\":\"block\",\"leaf\":151,\"vertices\":[2,8,11,15,18,21,43,44,49,54,70,77,94,97,98]},{\"tag\":\"block\",\"leaf\":152,\"vertices\":[4,5,11,13,20,24,27,34,54,61,77,84,86,99,100]},{\"tag\":\"block\",\"leaf\":153,\"vertices\":[3,5,12,14,18,24,25,36,59,61,72,83,87,99,100]},{\"tag\":\"block\",\"leaf\":154,\"vertices\":[4,6,8,10,19,23,27,35,58,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":155,\"vertices\":[3,7,9,10,17,23,26,36,53,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":156,\"vertices\":[1,2,4,9,15,24,42,46,59,72,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":157,\"vertices\":[1,2,3,13,16,23,45,53,58,68,73,83,94,97,98]},{\"tag\":\"block\",\"leaf\":158,\"vertices\":[1,2,4,14,16,23,43,53,58,65,78,86,90,97,98]},{\"tag\":\"block\",\"leaf\":159,\"vertices\":[3,5,10,15,17,22,26,44,53,59,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":160,\"vertices\":[4,5,10,15,19,21,35,42,54,58,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":161,\"vertices\":[3,5,10,16,18,22,25,45,59,61,72,78,83,99,100]},{\"tag\":\"block\",\"leaf\":162,\"vertices\":[4,5,10,16,20,21,34,43,54,61,73,77,86,99,100]},{\"tag\":\"block\",\"leaf\":163,\"vertices\":[1,2,4,9,15,24,42,49,54,72,77,84,94,97,98]},{\"tag\":\"block\",\"leaf\":164,\"vertices\":[1,2,3,13,16,23,45,53,58,65,78,86,90,97,98]},{\"tag\":\"block\",\"leaf\":165,\"vertices\":[1,2,4,14,16,23,43,53,58,68,73,83,94,97,98]},{\"tag\":\"block\",\"leaf\":166,\"vertices\":[3,5,10,15,17,22,25,45,59,61,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":167,\"vertices\":[4,5,10,15,19,21,34,43,54,61,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":168,\"vertices\":[3,5,10,16,18,22,26,44,53,59,78,80,83,99,100]},{\"tag\":\"block\",\"leaf\":169,\"vertices\":[4,5,10,16,20,21,35,42,54,58,73,80,86,99,100]},{\"tag\":\"block\",\"leaf\":170,\"vertices\":[2,6,8,13,16,23,27,45,58,65,78,86,90,97,98]},{\"tag\":\"block\",\"leaf\":171,\"vertices\":[1,9,12,14,15,24,36,42,49,54,72,84,94,97,98]},{\"tag\":\"block\",\"leaf\":172,\"vertices\":[2,8,11,13,15,24,27,44,46,59,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":173,\"vertices\":[4,5,11,18,20,21,35,42,54,58,70,80,86,99,100]},{\"tag\":\"block\",\"leaf\":174,\"vertices\":[3,5,12,18,20,22,26,44,53,59,70,80,83,99,100]},{\"tag\":\"block\",\"leaf\":175,\"vertices\":[4,6,10,17,19,21,34,43,52,61,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":176,\"vertices\":[3,7,10,17,19,22,25,45,52,61,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":177,\"vertices\":[2,6,8,13,16,23,27,45,58,68,73,83,94,97,98]},{\"tag\":\"block\",\"leaf\":178,\"vertices\":[1,9,12,14,15,24,36,42,46,59,72,87,90,97,98]},{\"tag\":\"block\",\"leaf\":179,\"vertices\":[2,8,11,13,15,24,27,44,49,54,77,84,94,97,98]},{\"tag\":\"block\",\"leaf\":180,\"vertices\":[4,5,11,18,20,21,34,43,54,61,70,77,86,99,100]},{\"tag\":\"block\",\"leaf\":181,\"vertices\":[3,5,12,18,20,22,25,45,59,61,70,72,83,99,100]},{\"tag\":\"block\",\"leaf\":182,\"vertices\":[4,6,10,17,19,21,35,42,52,58,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":183,\"vertices\":[3,7,10,17,19,22,26,44,52,53,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":184,\"vertices\":[2,6,8,13,16,24,27,44,49,73,77,83,94,97,98]},{\"tag\":\"block\",\"leaf\":185,\"vertices\":[1,9,12,14,15,23,36,43,53,59,65,87,90,97,98]},{\"tag\":\"block\",\"leaf\":186,\"vertices\":[2,8,11,13,15,23,27,45,54,58,68,84,94,97,98]},{\"tag\":\"block\",\"leaf\":187,\"vertices\":[4,5,11,18,20,22,25,43,59,61,70,77,83,99,100]},{\"tag\":\"block\",\"leaf\":188,\"vertices\":[3,5,12,18,20,21,34,45,54,61,70,72,86,99,100]},{\"tag\":\"block\",\"leaf\":189,\"vertices\":[4,6,10,17,19,22,26,42,52,58,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":190,\"vertices\":[3,7,10,17,19,21,35,44,52,53,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":191,\"vertices\":[2,8,13,15,16,23,27,45,54,58,68,73,94,97,98]},{\"tag\":\"block\",\"leaf\":192,\"vertices\":[1,9,14,15,16,24,36,42,46,59,72,78,90,97,98]},{\"tag\":\"block\",\"leaf\":193,\"vertices\":[2,8,13,15,16,24,27,44,49,54,73,77,94,97,98]},{\"tag\":\"block\",\"leaf\":194,\"vertices\":[3,4,5,18,20,21,34,54,61,70,72,77,86,99,100]},{\"tag\":\"block\",\"leaf\":195,\"vertices\":[3,4,5,18,20,22,25,59,61,70,72,77,83,99,100]},{\"tag\":\"block\",\"leaf\":196,\"vertices\":[3,4,10,17,19,21,35,52,53,58,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":197,\"vertices\":[3,4,10,17,19,22,26,52,53,58,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":198,\"vertices\":[2,5,6,8,13,24,27,44,59,73,77,83,87,97,98]},{\"tag\":\"block\",\"leaf\":199,\"vertices\":[1,9,10,12,14,23,36,43,53,59,73,83,87,97,98]},{\"tag\":\"block\",\"leaf\":200,\"vertices\":[2,8,10,11,13,23,27,45,54,58,78,84,86,97,98]},{\"tag\":\"block\",\"leaf\":201,\"vertices\":[1,5,11,18,20,22,43,44,53,59,70,77,83,99,100]},{\"tag\":\"block\",\"leaf\":202,\"vertices\":[2,5,12,18,20,21,42,45,54,58,70,72,86,99,100]},{\"tag\":\"block\",\"leaf\":203,\"vertices\":[1,6,10,17,19,22,42,45,52,58,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":204,\"vertices\":[2,7,10,17,19,21,43,44,52,53,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":205,\"vertices\":[2,8,13,15,17,24,27,44,46,59,73,77,87,97,98]},{\"tag\":\"block\",\"leaf\":206,\"vertices\":[1,9,14,16,20,23,36,43,53,59,68,73,83,97,98]},{\"tag\":\"block\",\"leaf\":207,\"vertices\":[2,8,13,16,18,23,27,45,54,58,65,78,86,97,98]},{\"tag\":\"block\",\"leaf\":208,\"vertices\":[3,5,13,18,20,22,26,44,53,59,70,77,83,99,100]},{\"tag\":\"block\",\"leaf\":209,\"vertices\":[4,5,14,18,20,21,35,42,54,58,70,72,86,99,100]},{\"tag\":\"block\",\"leaf\":210,\"vertices\":[3,8,10,17,19,22,25,45,52,58,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":211,\"vertices\":[4,9,10,17,19,21,34,43,52,53,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":212,\"vertices\":[2,8,13,18,19,23,27,45,54,58,65,78,88,97,98]},{\"tag\":\"block\",\"leaf\":213,\"vertices\":[1,9,14,18,19,24,36,42,49,54,72,78,88,97,98]},{\"tag\":\"block\",\"leaf\":214,\"vertices\":[2,8,13,17,20,24,27,44,46,59,73,77,88,97,98]},{\"tag\":\"block\",\"leaf\":215,\"vertices\":[5,8,14,18,20,21,35,41,54,58,70,72,86,99,100]},{\"tag\":\"block\",\"leaf\":216,\"vertices\":[5,9,13,18,20,22,26,41,53,59,70,77,83,99,100]},{\"tag\":\"block\",\"leaf\":217,\"vertices\":[9,10,13,17,19,21,34,41,52,53,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":218,\"vertices\":[8,10,14,17,19,22,25,41,52,58,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":219,\"vertices\":[2,8,13,15,17,24,27,44,46,59,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":220,\"vertices\":[1,9,14,16,20,23,36,43,53,59,68,73,83,99,100]},{\"tag\":\"block\",\"leaf\":221,\"vertices\":[2,8,13,16,18,23,27,45,54,58,65,78,86,99,100]},{\"tag\":\"block\",\"leaf\":222,\"vertices\":[3,5,13,18,20,22,26,44,53,59,70,77,83,97,98]},{\"tag\":\"block\",\"leaf\":223,\"vertices\":[4,5,14,18,20,21,35,42,54,58,70,72,86,97,98]},{\"tag\":\"block\",\"leaf\":224,\"vertices\":[3,8,10,17,19,22,25,45,52,58,72,78,84,97,98]},{\"tag\":\"block\",\"leaf\":225,\"vertices\":[4,9,10,17,19,21,34,43,52,53,73,77,87,97,98]},{\"tag\":\"block\",\"leaf\":226,\"vertices\":[2,5,6,8,13,24,27,44,59,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":227,\"vertices\":[1,9,10,12,14,23,36,43,53,59,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":228,\"vertices\":[2,8,10,11,13,23,27,45,54,58,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":229,\"vertices\":[1,5,11,18,20,22,43,44,53,59,70,77,83,97,98]},{\"tag\":\"block\",\"leaf\":230,\"vertices\":[2,5,12,18,20,21,42,45,54,58,70,72,86,97,98]},{\"tag\":\"block\",\"leaf\":231,\"vertices\":[1,6,10,17,19,22,42,45,52,58,72,78,84,97,98]},{\"tag\":\"block\",\"leaf\":232,\"vertices\":[2,7,10,17,19,21,43,44,52,53,73,77,87,97,98]},{\"tag\":\"block\",\"leaf\":233,\"vertices\":[2,5,8,14,17,24,25,41,58,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":234,\"vertices\":[1,8,10,14,20,23,35,41,54,58,72,84,86,99,100]},{\"tag\":\"block\",\"leaf\":235,\"vertices\":[2,9,10,13,18,23,26,41,53,59,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":236,\"vertices\":[1,5,13,18,19,22,42,45,54,58,65,78,88,97,98]},{\"tag\":\"block\",\"leaf\":237,\"vertices\":[2,5,14,17,20,21,43,44,53,59,68,73,88,97,98]},{\"tag\":\"block\",\"leaf\":238,\"vertices\":[1,8,10,17,20,22,43,44,46,59,73,77,88,97,98]},{\"tag\":\"block\",\"leaf\":239,\"vertices\":[2,9,10,18,19,21,42,45,49,54,72,78,88,97,98]},{\"tag\":\"block\",\"leaf\":240,\"vertices\":[2,9,13,18,20,23,26,41,53,59,70,77,83,99,100]},{\"tag\":\"block\",\"leaf\":241,\"vertices\":[1,9,13,17,19,24,34,41,52,53,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":242,\"vertices\":[2,8,14,17,19,24,25,41,52,58,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":243,\"vertices\":[5,9,14,17,20,21,36,43,53,59,68,73,88,97,98]},{\"tag\":\"block\",\"leaf\":244,\"vertices\":[5,8,13,18,19,22,27,45,54,58,65,78,88,97,98]},{\"tag\":\"block\",\"leaf\":245,\"vertices\":[9,10,14,18,19,21,36,42,49,54,72,78,88,97,98]},{\"tag\":\"block\",\"leaf\":246,\"vertices\":[8,10,13,17,20,22,27,44,46,59,73,77,88,97,98]},{\"tag\":\"block\",\"leaf\":247,\"vertices\":[2,4,9,15,18,21,42,49,54,70,72,77,94,97,98]},{\"tag\":\"block\",\"leaf\":248,\"vertices\":[1,3,13,16,19,22,45,52,53,58,65,78,90,97,98]},{\"tag\":\"block\",\"leaf\":249,\"vertices\":[2,4,14,16,17,21,43,52,53,58,68,73,94,97,98]},{\"tag\":\"block\",\"leaf\":250,\"vertices\":[3,5,14,15,17,24,25,36,59,61,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":251,\"vertices\":[4,5,13,15,19,24,27,34,54,61,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":252,\"vertices\":[3,9,10,16,18,23,26,36,53,59,78,80,83,99,100]},{\"tag\":\"block\",\"leaf\":253,\"vertices\":[4,8,10,16,20,23,27,35,54,58,73,80,86,99,100]},{\"tag\":\"block\",\"leaf\":254,\"vertices\":[2,7,14,16,17,21,43,44,52,53,68,73,94,97,98]},{\"tag\":\"block\",\"leaf\":255,\"vertices\":[1,8,11,15,20,22,43,44,46,59,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":256,\"vertices\":[2,9,12,15,18,21,42,45,49,54,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":257,\"vertices\":[4,5,6,13,19,24,27,34,61,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":258,\"vertices\":[3,5,7,14,17,24,25,36,61,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":259,\"vertices\":[4,8,10,11,20,23,27,35,54,58,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":260,\"vertices\":[3,9,10,12,18,23,26,36,53,59,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":261,\"vertices\":[4,9,14,15,18,21,35,42,49,54,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":262,\"vertices\":[3,8,13,16,19,22,25,45,52,58,65,78,90,97,98]},{\"tag\":\"block\",\"leaf\":263,\"vertices\":[4,9,14,16,17,21,34,43,52,53,68,73,94,97,98]},{\"tag\":\"block\",\"leaf\":264,\"vertices\":[3,14,15,17,19,24,25,36,49,61,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":265,\"vertices\":[4,13,15,17,19,24,27,34,46,61,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":266,\"vertices\":[3,9,16,18,20,23,26,36,53,59,68,80,83,99,100]},{\"tag\":\"block\",\"leaf\":267,\"vertices\":[4,8,16,18,20,23,27,35,54,58,65,80,86,99,100]},{\"tag\":\"block\",\"leaf\":268,\"vertices\":[4,6,13,17,19,24,27,34,52,61,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":269,\"vertices\":[3,9,12,18,20,23,26,36,53,59,70,80,83,99,100]},{\"tag\":\"block\",\"leaf\":270,\"vertices\":[4,8,11,18,20,23,27,35,54,58,70,80,86,99,100]},{\"tag\":\"block\",\"leaf\":271,\"vertices\":[8,11,13,15,20,22,27,44,46,59,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":272,\"vertices\":[9,12,14,15,18,21,36,42,49,54,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":273,\"vertices\":[6,8,13,16,19,22,27,45,52,58,65,78,90,97,98]},{\"tag\":\"block\",\"leaf\":274,\"vertices\":[7,9,14,16,17,21,36,43,52,53,68,73,94,97,98]},{\"tag\":\"block\",\"leaf\":275,\"vertices\":[2,6,13,16,20,23,27,45,59,61,68,73,83,99,100]},{\"tag\":\"block\",\"leaf\":276,\"vertices\":[1,9,12,15,17,24,36,42,46,59,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":277,\"vertices\":[2,8,11,15,19,24,27,44,49,54,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":278,\"vertices\":[4,5,9,11,20,21,34,43,53,70,77,86,90,97,98]},{\"tag\":\"block\",\"leaf\":279,\"vertices\":[3,5,8,12,18,22,25,45,58,70,72,83,94,97,98]},{\"tag\":\"block\",\"leaf\":280,\"vertices\":[4,6,10,14,19,21,35,42,52,58,72,87,90,97,98]},{\"tag\":\"block\",\"leaf\":281,\"vertices\":[3,7,10,13,17,22,26,44,52,53,77,84,94,97,98]},{\"tag\":\"block\",\"leaf\":282,\"vertices\":[2,5,7,8,11,24,27,44,54,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":283,\"vertices\":[1,7,10,11,14,23,36,43,54,61,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":284,\"vertices\":[2,6,10,12,13,23,27,45,59,61,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":285,\"vertices\":[1,5,6,12,18,22,42,45,58,70,72,83,94,97,98]},{\"tag\":\"block\",\"leaf\":286,\"vertices\":[2,5,7,11,20,21,43,44,53,70,77,86,90,97,98]},{\"tag\":\"block\",\"leaf\":287,\"vertices\":[1,7,10,11,17,22,43,44,52,53,77,84,94,97,98]},{\"tag\":\"block\",\"leaf\":288,\"vertices\":[2,6,10,12,19,21,42,45,52,58,72,87,90,97,98]},{\"tag\":\"block\",\"leaf\":289,\"vertices\":[2,7,13,16,18,23,27,45,54,61,65,78,86,99,100]},{\"tag\":\"block\",\"leaf\":290,\"vertices\":[1,9,11,15,19,24,36,42,49,54,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":291,\"vertices\":[2,8,12,15,17,24,27,44,46,59,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":292,\"vertices\":[4,5,6,14,20,21,35,42,58,70,72,86,90,97,98]},{\"tag\":\"block\",\"leaf\":293,\"vertices\":[3,5,7,13,18,22,26,44,53,70,77,83,94,97,98]},{\"tag\":\"block\",\"leaf\":294,\"vertices\":[4,9,10,11,19,21,34,43,52,53,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":295,\"vertices\":[3,8,10,12,17,22,25,45,52,58,72,84,94,97,98]},{\"tag\":\"block\",\"leaf\":296,\"vertices\":[2,5,6,8,12,24,27,44,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":297,\"vertices\":[1,6,10,12,14,23,36,43,59,61,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":298,\"vertices\":[2,7,10,11,13,23,27,45,54,61,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":299,\"vertices\":[1,5,7,11,18,22,43,44,53,70,77,83,94,97,98]},{\"tag\":\"block\",\"leaf\":300,\"vertices\":[2,5,6,12,20,21,42,45,58,70,72,86,90,97,98]},{\"tag\":\"block\",\"leaf\":301,\"vertices\":[1,6,10,12,17,22,42,45,52,58,72,84,94,97,98]},{\"tag\":\"block\",\"leaf\":302,\"vertices\":[2,7,10,11,19,21,43,44,52,53,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":303,\"vertices\":[0,2,3,8,17,25,45,52,58,68,72,84,94,97,98]},{\"tag\":\"block\",\"leaf\":304,\"vertices\":[0,1,4,14,20,35,42,46,58,70,72,86,90,97,98]},{\"tag\":\"block\",\"leaf\":305,\"vertices\":[0,2,3,13,18,26,44,49,53,70,77,83,94,97,98]},{\"tag\":\"block\",\"leaf\":306,\"vertices\":[0,5,13,16,18,27,34,45,54,61,65,78,86,99,100]},{\"tag\":\"block\",\"leaf\":307,\"vertices\":[0,5,14,16,20,25,36,43,59,61,68,73,83,99,100]},{\"tag\":\"block\",\"leaf\":308,\"vertices\":[0,8,10,15,17,27,35,44,46,59,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":309,\"vertices\":[0,9,10,15,19,26,36,42,49,54,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":310,\"vertices\":[0,1,2,7,19,43,44,52,53,65,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":311,\"vertices\":[0,1,2,11,18,43,44,49,53,70,77,83,94,97,98]},{\"tag\":\"block\",\"leaf\":312,\"vertices\":[0,1,2,12,20,42,45,46,58,70,72,86,90,97,98]},{\"tag\":\"block\",\"leaf\":313,\"vertices\":[0,5,6,8,10,27,35,44,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":314,\"vertices\":[0,5,7,9,10,26,36,42,54,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":315,\"vertices\":[0,5,10,11,13,27,34,45,54,61,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":316,\"vertices\":[0,5,10,12,14,25,36,43,59,61,73,83,87,99,100]},{\"tag\":\"block\",\"leaf\":317,\"vertices\":[1,2,4,5,14,24,42,54,58,72,78,84,86,95,96]},{\"tag\":\"block\",\"leaf\":318,\"vertices\":[1,2,3,8,10,23,45,54,58,72,78,84,86,95,96]},{\"tag\":\"block\",\"leaf\":319,\"vertices\":[1,2,4,9,10,23,43,53,59,73,77,83,87,95,96]},{\"tag\":\"block\",\"leaf\":320,\"vertices\":[1,5,10,15,19,22,42,45,54,58,72,78,84,95,96]},{\"tag\":\"block\",\"leaf\":321,\"vertices\":[2,5,10,15,17,21,43,44,53,59,73,77,87,95,96]},{\"tag\":\"block\",\"leaf\":322,\"vertices\":[1,5,10,16,20,22,43,44,53,59,73,77,83,95,96]},{\"tag\":\"block\",\"leaf\":323,\"vertices\":[2,5,10,16,18,21,42,45,54,58,72,78,86,95,96]},{\"tag\":\"block\",\"leaf\":324,\"vertices\":[1,2,4,5,14,24,42,54,58,72,78,84,86,97,98]},{\"tag\":\"block\",\"leaf\":325,\"vertices\":[1,2,3,8,10,23,45,54,58,72,78,84,86,97,98]},{\"tag\":\"block\",\"leaf\":326,\"vertices\":[1,2,4,9,10,23,43,53,59,73,77,83,87,97,98]},{\"tag\":\"block\",\"leaf\":327,\"vertices\":[1,5,10,15,19,22,42,45,54,58,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":328,\"vertices\":[2,5,10,15,17,21,43,44,53,59,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":329,\"vertices\":[1,5,10,16,20,22,43,44,53,59,73,77,83,99,100]},{\"tag\":\"block\",\"leaf\":330,\"vertices\":[2,5,10,16,18,21,42,45,54,58,72,78,86,99,100]},{\"tag\":\"block\",\"leaf\":331,\"vertices\":[1,2,4,9,15,23,43,53,59,65,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":332,\"vertices\":[1,2,3,13,16,24,44,49,53,73,77,83,94,97,98]},{\"tag\":\"block\",\"leaf\":333,\"vertices\":[1,2,4,14,16,24,42,46,58,72,78,86,90,97,98]},{\"tag\":\"block\",\"leaf\":334,\"vertices\":[3,5,10,15,17,21,35,44,53,59,73,80,87,99,100]},{\"tag\":\"block\",\"leaf\":335,\"vertices\":[4,5,10,15,19,22,26,42,54,58,78,80,84,99,100]},{\"tag\":\"block\",\"leaf\":336,\"vertices\":[3,5,10,16,18,21,34,45,54,61,72,78,86,99,100]},{\"tag\":\"block\",\"leaf\":337,\"vertices\":[4,5,10,16,20,22,25,43,59,61,73,77,83,99,100]},{\"tag\":\"block\",\"leaf\":338,\"vertices\":[2,4,8,16,18,23,27,54,58,65,78,80,86,99,100]},{\"tag\":\"block\",\"leaf\":339,\"vertices\":[1,3,14,15,19,24,36,49,54,61,72,78,84,99,100]},{\"tag\":\"block\",\"leaf\":340,\"vertices\":[2,4,13,15,17,24,27,46,59,61,73,77,87,99,100]},{\"tag\":\"block\",\"leaf\":341,\"vertices\":[4,5,14,15,18,21,35,42,54,58,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":342,\"vertices\":[3,5,13,15,20,22,26,44,53,59,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":343,\"vertices\":[4,9,10,16,17,21,34,43,52,53,73,77,94,97,98]},{\"tag\":\"block\",\"leaf\":344,\"vertices\":[3,8,10,16,19,22,25,45,52,58,72,78,90,97,98]},{\"tag\":\"block\",\"leaf\":345,\"vertices\":[2,4,5,8,11,24,27,54,58,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":346,\"vertices\":[1,3,7,10,14,23,36,54,61,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":347,\"vertices\":[2,4,6,10,13,23,27,59,61,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":348,\"vertices\":[1,5,12,15,18,22,42,45,54,58,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":349,\"vertices\":[2,5,11,15,20,21,43,44,53,59,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":350,\"vertices\":[1,7,10,16,17,22,43,44,52,53,73,77,94,97,98]},{\"tag\":\"block\",\"leaf\":351,\"vertices\":[2,6,10,16,19,21,42,45,52,58,72,78,90,97,98]},{\"tag\":\"block\",\"leaf\":352,\"vertices\":[1,2,5,9,13,24,41,53,59,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":353,\"vertices\":[1,2,9,10,13,23,41,53,59,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":354,\"vertices\":[1,2,8,10,14,23,41,54,58,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":355,\"vertices\":[1,5,10,17,20,22,43,44,53,59,73,77,88,97,98]},{\"tag\":\"block\",\"leaf\":356,\"vertices\":[2,5,10,18,19,21,42,45,54,58,72,78,88,97,98]},{\"tag\":\"block\",\"leaf\":357,\"vertices\":[1,5,10,18,19,22,42,45,54,58,72,78,88,97,98]},{\"tag\":\"block\",\"leaf\":358,\"vertices\":[2,5,10,17,20,21,43,44,53,59,73,77,88,97,98]},{\"tag\":\"block\",\"leaf\":359,\"vertices\":[1,2,4,5,14,24,42,54,58,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":360,\"vertices\":[1,2,3,8,10,23,45,54,58,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":361,\"vertices\":[1,2,4,9,10,23,43,53,59,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":362,\"vertices\":[1,5,10,15,19,22,42,45,54,58,72,78,84,97,98]},{\"tag\":\"block\",\"leaf\":363,\"vertices\":[2,5,10,15,17,21,43,44,53,59,73,77,87,97,98]},{\"tag\":\"block\",\"leaf\":364,\"vertices\":[1,5,10,16,20,22,43,44,53,59,73,77,83,97,98]},{\"tag\":\"block\",\"leaf\":365,\"vertices\":[2,5,10,16,18,21,42,45,54,58,72,78,86,97,98]},{\"tag\":\"block\",\"leaf\":366,\"vertices\":[2,3,4,5,13,24,25,59,61,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":367,\"vertices\":[1,3,4,9,10,23,35,53,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":368,\"vertices\":[2,3,4,8,10,23,26,54,58,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":369,\"vertices\":[1,5,15,16,20,22,43,44,53,59,65,77,90,97,98]},{\"tag\":\"block\",\"leaf\":370,\"vertices\":[2,5,15,16,18,21,42,45,54,58,68,72,94,97,98]},{\"tag\":\"block\",\"leaf\":371,\"vertices\":[1,10,15,16,19,22,42,45,46,58,72,78,90,97,98]},{\"tag\":\"block\",\"leaf\":372,\"vertices\":[2,10,15,16,17,21,43,44,49,53,73,77,94,97,98]},{\"tag\":\"block\",\"leaf\":373,\"vertices\":[2,4,5,6,13,24,27,59,61,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":374,\"vertices\":[1,3,9,10,12,23,36,53,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":375,\"vertices\":[2,4,8,10,11,23,27,54,58,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":376,\"vertices\":[1,5,11,15,20,22,43,44,53,59,70,77,90,97,98]},{\"tag\":\"block\",\"leaf\":377,\"vertices\":[2,5,12,15,18,21,42,45,54,58,70,72,94,97,98]},{\"tag\":\"block\",\"leaf\":378,\"vertices\":[1,6,10,16,19,22,42,45,52,58,72,78,90,97,98]},{\"tag\":\"block\",\"leaf\":379,\"vertices\":[2,7,10,16,17,21,43,44,52,53,73,77,94,97,98]},{\"tag\":\"block\",\"leaf\":380,\"vertices\":[0,1,2,5,10,43,44,53,59,73,77,83,87,95,96]},{\"tag\":\"block\",\"leaf\":381,\"vertices\":[0,1,2,5,10,43,44,53,59,73,77,83,87,97,98]},{\"tag\":\"block\",\"leaf\":382,\"vertices\":[0,1,2,5,10,43,44,53,59,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":383,\"vertices\":[0,1,2,5,10,42,45,54,58,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":384,\"vertices\":[0,1,2,5,15,43,44,53,59,65,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":385,\"vertices\":[0,1,2,10,16,43,44,49,53,73,77,83,94,97,98]},{\"tag\":\"block\",\"leaf\":386,\"vertices\":[0,1,2,10,16,42,45,46,58,72,78,86,90,97,98]},{\"tag\":\"block\",\"leaf\":387,\"vertices\":[0,1,3,5,10,35,44,53,59,73,80,83,87,99,100]},{\"tag\":\"block\",\"leaf\":388,\"vertices\":[0,2,4,5,10,26,42,54,58,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":389,\"vertices\":[0,1,3,5,10,34,45,54,61,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":390,\"vertices\":[0,2,4,5,10,25,43,59,61,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":391,\"vertices\":[1,2,4,5,11,24,42,54,58,78,80,84,86,99,100]},{\"tag\":\"block\",\"leaf\":392,\"vertices\":[1,2,3,7,10,23,45,54,61,72,78,84,86,99,100]},{\"tag\":\"block\",\"leaf\":393,\"vertices\":[1,2,4,6,10,23,43,59,61,73,77,83,87,99,100]},{\"tag\":\"block\",\"leaf\":394,\"vertices\":[1,5,10,12,15,22,42,45,54,58,72,84,94,97,98]},{\"tag\":\"block\",\"leaf\":395,\"vertices\":[2,5,10,11,15,21,43,44,53,59,77,87,90,97,98]},{\"tag\":\"block\",\"leaf\":396,\"vertices\":[1,5,7,10,16,22,43,44,53,73,77,83,94,97,98]},{\"tag\":\"block\",\"leaf\":397,\"vertices\":[2,5,6,10,16,21,42,45,58,72,78,86,90,97,98]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[17,18,48,54,57,62,66,73,75,81,83,84,90,92,96,97,98,99]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[19,20,51,56,59,62,69,74,78,81,86,87,91,94,96,97,98,100]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[8,9,30,37,42,44,53,58,61,71,76,79,89,93,95,97,99,100]}]}"
  "p cnf 233 1244\n-23 -22 0\n-24 -22 0\n-24 -23 0\n-25 -11 0\n-25 -22 0\n-25 -23 0\n-25 -24 0\n-26 -2 0\n-26 -22 0\n-27 -22 0\n-27 -25 0\n-27 -26 0\n-28 -2 0\n-28 -22 0\n-28 -26 0\n-28 -27 0\n-35 -3 0\n-35 -23 0\n-35 -24 0\n-35 -26 0\n-36 -3 0\n-36 -23 0\n-36 -25 0\n-36 -27 0\n-36 -35 0\n-37 -3 0\n-37 -5 0\n-37 -23 0\n-37 -35 0\n-37 -36 0\n-42 -28 0\n-42 -37 0\n-43 -9 0\n-43 -24 0\n-43 -26 0\n-43 -28 0\n-43 -35 0\n-43 -42 0\n-44 -25 0\n-44 -27 0\n-44 -28 0\n-44 -36 0\n-44 -42 0\n-44 -43 0\n-45 -10 0\n-45 -24 0\n-45 -26 0\n-45 -35 0\n-45 -37 0\n-45 -42 0\n-45 -43 0\n-46 -5 0\n-46 -25 0\n-46 -27 0\n-46 -36 0\n-46 -37 0\n-46 -42 0\n-46 -44 0\n-46 -45 0\n-47 -6 0\n-47 -22 0\n-47 -24 0\n-47 -26 0\n-50 -23 0\n-50 -24 0\n-50 -35 0\n-50 -47 0\n-53 -16 0\n-53 -24 0\n-53 -47 0\n-53 -50 0\n-54 -9 0\n-54 -26 0\n-54 -28 0\n-54 -43 0\n-54 -47 0\n-55 -26 0\n-55 -47 0\n-55 -53 0\n-55 -54 0\n-57 -23 0\n-57 -50 0\n-57 -53 0\n-57 -55 0\n-59 -8 0\n-59 -10 0\n-59 -35 0\n-59 -37 0\n-59 -45 0\n-59 -50 0\n-60 -35 0\n-60 -50 0\n-60 -53 0\n-60 -55 0\n-60 -57 0\n-60 -59 0\n-62 -42 0\n-62 -43 0\n-62 -45 0\n-62 -54 0\n-62 -59 0\n-66 -11 0\n-66 -22 0\n-66 -25 0\n-66 -27 0\n-66 -47 0\n-69 -23 0\n-69 -25 0\n-69 -36 0\n-69 -50 0\n-69 -57 0\n-69 -66 0\n-71 -11 0\n-71 -25 0\n-71 -66 0\n-71 -69 0\n-73 -27 0\n-73 -28 0\n-73 -44 0\n-73 -54 0\n-73 -66 0\n-74 -27 0\n-74 -66 0\n-74 -71 0\n-74 -73 0\n-78 -36 0\n-78 -37 0\n-78 -46 0\n-78 -59 0\n-78 -69 0\n-79 -13 0\n-79 -36 0\n-79 -69 0\n-79 -71 0\n-79 -74 0\n-79 -78 0\n-81 -42 0\n-81 -44 0\n-81 -46 0\n-81 -62 0\n-81 -73 0\n-81 -78 0\n-84 -16 0\n-84 -22 0\n-84 -47 0\n-84 -53 0\n-84 -55 0\n-84 -66 0\n-85 -19 0\n-85 -22 0\n-85 -47 0\n-85 -66 0\n-85 -71 0\n-85 -74 0\n-85 -84 0\n-87 -23 0\n-87 -50 0\n-87 -53 0\n-87 -57 0\n-87 -60 0\n-87 -69 0\n-87 -84 0\n-88 -23 0\n-88 -50 0\n-88 -57 0\n-88 -69 0\n-88 -71 0\n-88 -79 0\n-88 -85 0\n-88 -87 0\n-89 -16 0\n-89 -52 0\n-89 -53 0\n-89 -71 0\n-89 -84 0\n-89 -85 0\n-89 -87 0\n-89 -88 0\n-91 -18 0\n-91 -55 0\n-91 -74 0\n-91 -84 0\n-91 -85 0\n-95 -20 0\n-95 -52 0\n-95 -60 0\n-95 -79 0\n-95 -87 0\n-95 -88 0\n-95 -89 0\n-95 -91 0\n-96 -42 0\n-96 -89 0\n-97 -42 0\n-97 -89 0\n-98 -42 0\n-98 -62 0\n-98 -81 0\n-99 -42 0\n-99 -62 0\n-99 -81 0\n-100 -89 0\n-100 -91 0\n-100 -95 0\n-101 -89 0\n-2 1 23 24 25 29 30 31 32 0\n-23 2 26 27 28 31 32 0\n-24 2 27 28 30 32 0\n-25 2 26 28 29 31 0\n-26 1 23 25 30 32 0\n-27 1 23 24 29 31 0\n-28 1 23 24 25 29 30 0\n-22 3 35 36 37 38 39 0\n-24 3 34 36 37 39 0\n-25 3 33 35 37 38 0\n-35 1 22 25 34 39 0\n-36 1 22 24 33 38 0\n-37 1 22 24 25 33 34 0\n-1 6 47 48 49 50 51 52 53 0\n-6 1 22 23 25 48 49 51 52 0\n-22 6 50 51 52 53 0\n-23 6 47 48 49 53 0\n-25 6 47 49 50 52 53 0\n-47 1 23 25 51 52 0\n-50 1 22 25 48 49 0\n-53 1 22 23 25 48 51 0\n-22 11 68 69 70 71 0\n-23 11 65 66 67 71 0\n-24 11 66 67 69 70 71 0\n-66 1 23 24 68 70 0\n-69 1 22 24 65 67 0\n-22 4 40 41 42 43 44 0\n-26 4 34 41 42 44 0\n-27 4 33 40 42 43 0\n-42 2 22 26 27 33 34 0\n-43 2 22 27 34 41 0\n-44 2 22 26 33 40 0\n-2 7 47 48 49 54 55 56 0\n-22 7 54 55 56 0\n-27 7 47 49 54 55 0\n-28 7 47 48 49 55 0\n-47 2 27 28 56 0\n-54 2 22 27 48 49 0\n-55 2 22 27 28 48 56 0\n-22 12 72 73 74 0\n-28 12 65 66 67 74 0\n-73 2 22 26 65 67 0\n-74 2 22 26 28 65 72 0\n-3 5 29 30 40 41 42 45 46 0\n-23 5 40 41 42 45 46 0\n-35 5 30 41 42 46 0\n-36 5 29 40 42 45 0\n-42 3 23 29 30 35 36 0\n-45 3 23 30 36 41 0\n-46 3 23 29 35 40 0\n-3 8 50 51 52 59 60 61 0\n-23 8 59 60 61 0\n-37 8 50 51 52 60 0\n-50 3 36 37 61 0\n-59 3 23 36 51 52 0\n-60 3 23 36 37 51 61 0\n-23 13 77 78 79 0\n-35 13 69 70 78 79 0\n-37 13 68 69 70 79 0\n-69 3 35 37 77 0\n-78 3 23 35 68 70 0\n-79 3 23 35 37 68 77 0\n-4 5 31 32 37 38 39 45 46 0\n-28 5 37 38 39 45 46 0\n-37 4 28 31 32 43 44 0\n-43 5 32 37 39 46 0\n-44 5 31 37 38 45 0\n-45 4 28 32 39 44 0\n-46 4 28 31 38 43 0\n-9 4 28 42 44 56 64 0\n-28 9 62 64 0\n-42 9 54 56 0\n-54 4 42 44 64 0\n-62 4 28 44 56 0\n-14 4 28 42 43 72 80 0\n-28 14 80 81 0\n-42 14 72 73 0\n-43 14 73 81 0\n-73 4 42 43 80 0\n-81 4 28 43 72 0\n-10 5 37 42 46 61 64 0\n-37 10 62 64 0\n-42 10 59 61 0\n-46 10 59 62 0\n-59 5 42 46 64 0\n-62 5 37 46 61 0\n-5 15 77 78 80 81 0\n-15 5 37 42 45 77 80 0\n-37 15 80 81 0\n-42 15 77 78 0\n-45 15 78 81 0\n-78 5 42 45 80 0\n-81 5 37 45 77 0\n-24 7 54 55 57 0\n-26 6 50 53 57 0\n-53 7 26 29 31 54 0\n-54 6 24 29 50 53 57 0\n-55 6 24 29 31 50 0\n-6 8 33 35 38 58 59 60 0\n-24 8 58 59 60 0\n-35 6 47 53 58 0\n-53 8 33 35 38 59 0\n-59 6 24 33 47 53 58 0\n-60 6 24 33 38 47 0\n-6 16 65 68 83 84 86 87 89 0\n-16 6 24 47 50 65 68 83 86 0\n-24 16 83 84 86 87 89 0\n-47 16 68 86 87 89 0\n-50 16 65 83 84 89 0\n-84 6 24 50 68 86 0\n-87 6 24 47 65 83 0\n-9 7 26 33 40 47 55 58 63 0\n-26 9 58 62 63 0\n-43 7 47 55 58 63 0\n-47 9 40 43 62 63 0\n-55 9 33 40 43 62 0\n-62 7 26 33 47 55 58 0\n-18 7 26 47 54 65 72 83 90 0\n-47 18 72 90 91 0\n-54 18 65 83 84 91 0\n-84 7 26 54 72 90 0\n-8 10 29 40 45 57 62 63 0\n-35 10 57 62 63 0\n-45 8 50 57 60 63 0\n-50 10 40 45 62 63 0\n-60 10 29 40 45 62 0\n-62 8 29 35 50 57 60 0\n-35 20 86 87 94 95 0\n-50 20 77 94 95 0\n-59 20 68 86 87 95 0\n-87 8 35 59 77 94 0\n-95 8 35 50 59 68 77 0\n-9 10 31 38 45 59 0\n-10 9 31 38 43 54 0\n-43 10 59 0\n-45 9 54 0\n-54 10 38 45 59 0\n-59 9 31 43 54 0\n-9 72 80 90 96 98 100 0\n-43 90 96 98 100 0\n-54 80 96 98 100 0\n-62 72 90 100 0\n-96 9 43 54 72 0\n-98 9 43 54 72 90 0\n-100 9 43 54 62 72 80 0\n-10 77 80 94 96 98 101 0\n-45 94 96 98 101 0\n-59 80 96 98 101 0\n-62 77 94 101 0\n-98 10 45 59 77 94 0\n-101 10 45 59 62 77 80 0\n-11 12 27 30 32 73 74 75 0\n-12 11 25 30 32 69 71 75 0\n-25 12 73 74 75 0\n-27 11 69 71 75 0\n-69 12 27 32 73 74 0\n-71 12 27 30 32 73 0\n-73 11 25 30 69 71 75 0\n-74 11 25 30 32 69 0\n-25 13 76 78 79 0\n-36 11 66 71 76 0\n-71 13 34 36 39 78 0\n-78 11 25 34 66 71 76 0\n-79 11 25 34 39 66 0\n-11 17 48 51 83 85 86 88 89 0\n-25 17 83 85 86 88 89 0\n-66 17 51 86 88 89 0\n-69 17 48 83 85 89 0\n-85 11 25 51 69 86 0\n-88 11 25 48 66 83 0\n-89 11 25 48 51 66 69 0\n-12 14 34 41 44 76 81 82 0\n-27 14 76 81 82 0\n-44 12 66 74 76 82 0\n-66 14 41 44 81 82 0\n-74 14 34 41 44 81 0\n-81 12 27 34 66 74 76 0\n-27 19 83 85 90 91 0\n-66 19 56 90 91 0\n-73 19 48 83 85 91 0\n-85 12 27 56 73 90 0\n-91 12 27 48 56 66 73 0\n-36 15 75 81 82 0\n-46 13 69 75 79 82 0\n-69 15 41 46 81 82 0\n-79 15 30 41 46 81 0\n-81 13 30 36 69 75 79 0\n-13 21 51 61 86 88 94 95 0\n-21 13 36 51 61 69 78 86 94 0\n-36 21 86 88 94 95 0\n-69 21 61 94 95 0\n-78 21 51 86 88 95 0\n-88 13 36 61 78 94 0\n-95 13 36 51 61 69 78 0\n-14 15 32 39 46 78 0\n-44 15 78 0\n-46 14 73 0\n-73 15 39 46 78 0\n-78 14 32 44 73 0\n-14 56 64 90 96 99 100 0\n-44 90 96 99 100 0\n-73 64 96 99 100 0\n-81 56 90 100 0\n-96 14 44 56 73 0\n-99 14 44 56 73 90 0\n-100 14 44 56 64 73 81 0\n-15 61 64 94 96 99 101 0\n-46 94 96 99 101 0\n-78 64 96 99 101 0\n-81 61 94 101 0\n-96 15 46 61 78 0\n-99 15 46 61 78 94 0\n-101 15 46 61 64 78 81 0\n-17 16 49 52 53 67 70 84 87 0\n-53 17 67 70 71 85 88 0\n-71 16 49 52 53 84 87 0\n-84 17 52 70 71 88 0\n-85 16 52 53 70 87 0\n-87 17 49 67 71 85 0\n-88 16 49 53 67 84 0\n-16 18 55 57 91 92 0\n-18 16 53 57 87 89 92 0\n-53 18 91 92 0\n-55 16 87 89 92 0\n-89 18 55 57 0\n-91 16 53 57 87 0\n-20 16 53 58 84 89 93 0\n-53 20 93 95 0\n-60 16 84 89 93 0\n-84 20 60 95 0\n-89 20 58 60 0\n-95 16 53 58 84 0\n-19 17 71 75 88 89 92 0\n-71 19 91 92 0\n-74 17 88 89 92 0\n-88 19 74 91 0\n-89 19 74 75 0\n-91 17 71 75 88 0\n-21 17 71 76 85 89 93 0\n-71 21 93 95 0\n-79 17 85 89 93 0\n-85 21 79 95 0\n-89 21 76 79 0\n-95 17 71 76 85 0\n-18 19 49 67 74 85 0\n-55 19 67 74 85 0\n-74 18 49 55 84 0\n-84 19 74 0\n-85 18 55 0\n-18 58 63 93 97 98 100 0\n-55 93 97 98 100 0\n-84 63 97 98 100 0\n-91 58 63 98 0\n-97 18 55 58 84 0\n-100 18 55 58 63 84 0\n-19 76 82 93 97 99 100 0\n-74 93 97 99 100 0\n-85 82 97 99 100 0\n-91 76 82 99 0\n-97 19 74 76 85 0\n-99 19 74 76 85 91 93 0\n-100 19 74 76 82 85 0\n-20 21 52 70 79 88 0\n-60 21 70 79 88 0\n-79 20 52 60 87 0\n-87 21 79 0\n-88 20 60 0\n-20 57 63 92 97 98 101 0\n-60 92 97 98 101 0\n-87 63 97 98 101 0\n-95 57 63 98 0\n-97 20 57 60 87 0\n-98 20 57 60 87 92 95 0\n-101 20 57 60 63 87 0\n-21 75 82 92 97 99 101 0\n-79 92 97 99 101 0\n-88 82 97 99 101 0\n-95 75 82 99 0\n-97 21 75 79 88 0\n-99 21 75 79 88 92 95 0\n-101 21 75 79 82 88 0\n-29 68 0\n-68 29 0\n-30 51 0\n-51 30 0\n-31 72 0\n-72 31 0\n-32 56 0\n-56 32 0\n-33 65 0\n-65 33 0\n-34 48 0\n-48 34 0\n-38 77 0\n-77 38 0\n-39 61 0\n-61 39 0\n-40 80 0\n-80 40 0\n-41 64 0\n-64 41 0\n-49 58 0\n-58 49 0\n-52 57 0\n-57 52 0\n-63 0\n-67 76 0\n-76 67 0\n-70 75 0\n-75 70 0\n-82 0\n-83 93 0\n-93 83 0\n-86 92 0\n-92 86 0\n-90 0\n-94 0\n-98 99 0\n-99 98 0\n-100 101 0\n-101 100 0\n-1 102 0\n-2 103 0\n-3 104 0\n-4 105 0\n-5 106 0\n-6 107 0\n-7 108 0\n-109 8 0\n-8 109 0\n-110 9 0\n-9 110 0\n-111 10 0\n-10 111 0\n-11 112 0\n-12 113 0\n-13 114 0\n-14 115 0\n-15 116 0\n-16 117 0\n-17 118 0\n-18 119 0\n-19 120 0\n-20 121 0\n-21 122 0\n-103 123 0\n-102 123 0\n-106 124 0\n-105 124 0\n-105 -106 125 0\n-124 126 0\n-125 127 0\n-104 126 0\n-104 -124 127 0\n-126 128 0\n-127 129 0\n-123 128 0\n-123 -126 129 0\n-108 130 0\n-107 130 0\n-107 -108 131 0\n-132 110 111 0\n-111 132 0\n-110 132 0\n-110 -111 133 0\n-134 109 132 0\n-132 134 0\n-133 135 0\n-109 134 0\n-109 -132 135 0\n-109 -133 136 0\n-134 137 0\n-135 138 0\n-136 139 0\n-130 137 0\n-130 -134 138 0\n-130 -135 139 0\n-130 -136 140 0\n-131 138 0\n-131 -134 139 0\n-137 141 0\n-139 143 0\n-128 141 0\n-128 -137 142 0\n-128 -138 143 0\n-128 -139 144 0\n-128 -140 145 0\n-129 142 0\n-129 -137 143 0\n-129 -139 145 0\n-113 146 0\n-112 146 0\n-112 -113 147 0\n-116 148 0\n-115 148 0\n-115 -116 149 0\n-148 150 0\n-149 151 0\n-114 150 0\n-114 -148 151 0\n-114 -149 152 0\n-150 153 0\n-151 154 0\n-146 153 0\n-146 -150 154 0\n-146 -151 155 0\n-146 -152 156 0\n-147 154 0\n-147 -150 155 0\n-119 157 0\n-118 157 0\n-118 -119 158 0\n-157 159 0\n-158 160 0\n-117 159 0\n-117 -157 160 0\n-122 161 0\n-121 161 0\n-121 -122 162 0\n-161 163 0\n-162 164 0\n-120 163 0\n-120 -161 164 0\n-120 -162 165 0\n-163 166 0\n-164 167 0\n-159 166 0\n-159 -163 167 0\n-159 -164 168 0\n-159 -165 169 0\n-160 167 0\n-160 -163 168 0\n-160 -164 169 0\n-168 172 0\n-169 173 0\n-153 170 0\n-153 -166 171 0\n-153 -167 172 0\n-153 -168 173 0\n-153 -169 174 0\n-154 171 0\n-154 -166 172 0\n-154 -167 173 0\n-154 -168 174 0\n-154 -169 175 0\n-155 172 0\n-155 -166 173 0\n-155 -167 174 0\n-155 -168 175 0\n-156 173 0\n-175 176 0\n-141 -174 176 0\n-142 -173 176 0\n-143 -172 176 0\n-144 -171 176 0\n-145 -170 176 0\n-176 0\n-177 42 62 81 0\n-42 177 0\n-62 177 0\n-81 177 0\n-178 89 91 95 0\n-89 178 0\n-91 178 0\n-95 178 0\n-179 53 55 60 0\n-53 179 0\n-55 179 0\n-60 179 0\n-180 28 54 73 0\n-28 180 0\n-54 180 0\n-73 180 0\n-181 37 59 78 0\n-37 181 0\n-59 181 0\n-78 181 0\n-182 71 74 79 0\n-71 182 0\n-74 182 0\n-79 182 0\n-183 22 47 66 84 85 0\n-22 183 0\n-47 183 0\n-84 183 0\n-85 183 0\n-184 25 27 36 44 46 0\n-25 184 0\n-27 184 0\n-36 184 0\n-44 184 0\n-46 184 0\n-185 24 26 35 43 45 0\n-24 185 0\n-26 185 0\n-35 185 0\n-43 185 0\n-45 185 0\n-186 23 50 69 87 88 0\n-23 186 0\n-69 186 0\n-88 186 0\n-187 177 178 0\n-178 187 0\n-188 177 0\n-177 187 0\n-188 178 0\n-177 -178 188 0\n-189 180 181 0\n-190 180 0\n-190 181 0\n-180 -181 190 0\n-191 179 190 0\n-192 179 0\n-191 189 0\n-192 190 0\n-179 -190 192 0\n-193 187 192 0\n-194 187 0\n-193 188 191 0\n-194 188 192 0\n-187 -192 194 0\n-195 188 0\n-194 191 0\n-195 192 0\n-196 182 183 0\n-197 182 0\n-197 183 0\n-182 -183 197 0\n-198 185 186 0\n-199 185 0\n-199 186 0\n-200 184 199 0\n-201 184 0\n-200 198 0\n-201 199 0\n-184 -199 201 0\n-202 196 0\n-202 197 201 0\n-203 197 0\n-202 200 0\n-203 201 0\n-197 -201 203 0\n-204 193 0\n-204 194 203 0\n-204 195 202 0\n-194 -203 205 0\n204 0\n-205 0\n-206 96 98 100 0\n-96 206 0\n-98 206 0\n-100 206 0\n-207 97 99 101 0\n-97 207 0\n-99 207 0\n-101 207 0\n-208 29 31 33 38 40 0\n-29 208 0\n-31 208 0\n-33 208 0\n-38 208 0\n-40 208 0\n-209 30 32 34 39 41 0\n-30 209 0\n-32 209 0\n-34 209 0\n-39 209 0\n-41 209 0\n-210 49 52 63 0\n-49 210 0\n-52 210 0\n-211 48 58 65 67 83 0\n-48 211 0\n-58 211 0\n-65 211 0\n-67 211 0\n-83 211 0\n-212 51 56 61 64 0\n-51 212 0\n-56 212 0\n-61 212 0\n-64 212 0\n-213 70 76 82 0\n-70 213 0\n-76 213 0\n-214 68 72 77 80 0\n-68 214 0\n-72 214 0\n-77 214 0\n-80 214 0\n-215 57 75 86 0\n-57 215 0\n-75 215 0\n-86 215 0\n-216 90 92 93 94 0\n-92 216 0\n-93 216 0\n-207 217 0\n-218 206 0\n-206 217 0\n-218 207 0\n-219 209 210 0\n-210 219 0\n-209 219 0\n-220 208 219 0\n-219 220 0\n-208 220 0\n-220 221 0\n-217 221 0\n-222 218 220 0\n-217 -220 222 0\n-223 212 213 0\n-213 223 0\n-212 223 0\n-224 211 223 0\n-223 224 0\n-211 224 0\n-211 -223 225 0\n-226 215 216 0\n-216 226 0\n-215 226 0\n-215 -216 227 0\n-228 214 226 0\n-226 228 0\n-227 229 0\n-214 228 0\n-230 224 228 0\n-228 230 0\n-229 231 0\n-224 230 0\n-224 -228 231 0\n-225 231 0\n-232 222 230 0\n-221 -231 233 0\n-222 -230 233 0\n232 0\n-233 0\n-4 -8 -14 -18 -19 -23 -27 -45 -53 -54 -71 -78 -95 -98 -99 0\n-2 -7 -13 -18 -19 -23 -43 -46 -53 -59 -71 -73 -95 -98 -99 0\n-2 -6 -9 -10 -21 -25 -35 -42 -55 -73 -78 -85 -87 -100 -101 0\n-2 -10 -15 -18 -19 -24 -37 -44 -54 -60 -66 -79 -89 -98 -99 0\n-2 -8 -17 -18 -19 -23 -44 -45 -53 -54 -66 -78 -95 -98 -99 0\n-2 -6 -9 -10 -15 -25 -35 -42 -55 -73 -79 -85 -87 -100 -101 0\n-2 -7 -13 -20 -21 -23 -43 -46 -53 -59 -71 -73 -91 -98 -99 0\n-2 -8 -17 -20 -21 -23 -44 -45 -53 -54 -66 -78 -91 -98 -99 0\n-4 -8 -14 -20 -21 -23 -27 -45 -53 -54 -71 -78 -91 -98 -99 0\n-4 -9 -15 -16 -19 -22 -36 -45 -50 -55 -71 -73 -95 -98 -99 0\n-2 -10 -15 -16 -20 -25 -37 -43 -50 -55 -73 -79 -85 -96 -97 0\n-2 -6 -8 -10 -15 -25 -37 -43 -55 -73 -79 -85 -87 -96 -97 0\n-2 -4 -5 -6 -21 -25 -35 -55 -62 -73 -78 -85 -87 -100 -101 0\n-2 -5 -10 -16 -21 -23 -43 -47 -60 -71 -73 -78 -91 -98 -99 0\n-2 -8 -15 -17 -20 -23 -44 -45 -53 -54 -66 -79 -91 -98 -99 0\n-2 -3 -4 -9 -16 -25 -45 -50 -55 -73 -78 -85 -95 -98 -99 0\n-2 -3 -4 -9 -16 -25 -45 -47 -60 -73 -78 -88 -91 -98 -99 0\n-2 -8 -10 -15 -17 -24 -37 -44 -54 -69 -74 -84 -95 -98 -99 0\n-2 -8 -10 -15 -17 -24 -37 -44 -54 -66 -79 -87 -91 -98 -99 0\n-2 -8 -10 -15 -17 -25 -37 -43 -47 -73 -79 -87 -91 -98 -99 0\n-2 -10 -15 -16 -17 -24 -37 -44 -54 -60 -66 -79 -91 -98 -99 0\n-2 -6 -8 -10 -15 -25 -37 -43 -55 -73 -79 -85 -87 -98 -99 0\n-2 -10 -15 -16 -20 -25 -37 -43 -50 -55 -73 -79 -85 -98 -99 0\n-2 -10 -15 -18 -21 -24 -37 -44 -54 -60 -69 -74 -89 -98 -99 0\n-2 -10 -15 -16 -20 -25 -37 -43 -50 -55 -73 -79 -85 -100 -101 0\n-2 -6 -8 -10 -15 -25 -37 -43 -55 -73 -79 -85 -87 -100 -101 0\n-2 -6 -10 -14 -20 -25 -35 -42 -54 -74 -78 -84 -88 -100 -101 0\n-2 -9 -15 -19 -21 -24 -36 -42 -55 -59 -71 -73 -87 -100 -101 0\n-2 -4 -9 -16 -21 -23 -45 -47 -60 -71 -73 -78 -91 -98 -99 0\n-2 -7 -14 -17 -20 -23 -43 -46 -53 -59 -66 -79 -91 -98 -99 0\n-4 -9 -14 -16 -21 -23 -27 -45 -47 -60 -71 -78 -91 -98 -99 0\n-4 -8 -15 -18 -20 -25 -26 -37 -53 -62 -73 -79 -85 -100 -101 0\n-2 -8 -15 -17 -19 -24 -37 -44 -55 -62 -66 -79 -87 -100 -101 0\n-2 -6 -7 -10 -13 -25 -37 -43 -60 -74 -81 -84 -88 -100 -101 0\n-2 -7 -15 -17 -21 -24 -37 -44 -60 -62 -69 -74 -84 -100 -101 0\n-2 -6 -8 -10 -12 -25 -37 -43 -55 -79 -81 -85 -87 -100 -101 0\n-1 -2 -5 -10 -20 -35 -44 -53 -54 -66 -78 -88 -91 -98 -99 0\n-1 -2 -3 -7 -18 -43 -46 -53 -59 -69 -73 -85 -95 -98 -99 0\n-2 -3 -4 -6 -14 -25 -45 -54 -60 -74 -78 -84 -88 -96 -97 0\n-2 -3 -4 -6 -14 -25 -45 -54 -60 -74 -78 -84 -88 -98 -99 0\n-2 -3 -4 -9 -16 -24 -46 -55 -59 -69 -73 -85 -95 -98 -99 0\n-2 -4 -10 -17 -21 -24 -37 -54 -60 -69 -74 -81 -84 -100 -101 0\n-2 -4 -6 -10 -13 -25 -37 -54 -60 -74 -81 -84 -88 -100 -101 0\n-2 -3 -6 -9 -15 -25 -42 -55 -59 -73 -79 -85 -87 -100 -101 0\n-2 -3 -4 -6 -14 -25 -45 -54 -60 -74 -78 -84 -88 -100 -101 0\n-2 -4 -5 -6 -15 -25 -35 -55 -62 -73 -79 -85 -87 -100 -101 0\n-2 -4 -6 -8 -15 -25 -37 -55 -62 -73 -79 -85 -87 -100 -101 0\n-1 -2 -3 -6 -11 -43 -46 -55 -59 -73 -79 -85 -87 -96 -97 0\n-1 -2 -3 -6 -11 -43 -46 -55 -59 -73 -79 -85 -87 -98 -99 0\n-1 -2 -3 -6 -16 -43 -46 -55 -59 -69 -73 -85 -95 -98 -99 0\n-2 -3 -4 -6 -13 -25 -45 -54 -60 -74 -81 -84 -88 -100 -101 0\n-5 -7 -15 -20 -21 -22 -36 -43 -53 -59 -71 -73 -91 -98 -99 0\n-4 -9 -13 -18 -19 -23 -26 -46 -53 -59 -71 -73 -95 -98 -99 0\n-5 -10 -12 -20 -21 -22 -35 -44 -53 -54 -71 -78 -91 -98 -99 0\n-9 -10 -12 -16 -20 -25 -28 -37 -50 -55 -79 -81 -85 -100 -101 0\n-9 -10 -13 -16 -18 -25 -28 -37 -47 -60 -74 -81 -88 -100 -101 0\n-7 -14 -15 -17 -21 -24 -28 -37 -60 -62 -69 -74 -84 -100 -101 0\n-8 -14 -15 -17 -19 -24 -28 -37 -55 -62 -66 -79 -87 -100 -101 0\n-3 -8 -12 -20 -21 -22 -44 -45 -53 -54 -71 -78 -91 -98 -99 0\n-2 -8 -12 -18 -19 -23 -44 -45 -53 -54 -71 -78 -95 -98 -99 0\n-3 -7 -13 -20 -21 -22 -43 -46 -53 -59 -71 -73 -91 -98 -99 0\n-6 -7 -9 -10 -13 -25 -28 -37 -60 -74 -81 -84 -88 -100 -101 0\n-6 -8 -9 -10 -12 -25 -28 -37 -55 -79 -81 -85 -87 -100 -101 0\n-8 -11 -12 -14 -15 -24 -28 -37 -55 -62 -79 -85 -87 -100 -101 0\n-7 -11 -13 -14 -15 -24 -28 -37 -60 -62 -74 -84 -88 -100 -101 0\n-3 -6 -9 -10 -19 -25 -26 -42 -60 -73 -78 -84 -88 -100 -101 0\n-2 -11 -14 -15 -20 -24 -36 -42 -54 -59 -74 -84 -88 -100 -101 0\n-3 -11 -14 -15 -18 -24 -27 -42 -54 -59 -79 -85 -87 -100 -101 0\n-2 -6 -15 -18 -19 -23 -44 -45 -54 -60 -66 -79 -89 -98 -99 0\n-3 -6 -14 -20 -21 -22 -43 -46 -55 -59 -69 -74 -89 -98 -99 0\n-2 -10 -11 -18 -19 -23 -43 -46 -47 -60 -73 -79 -89 -98 -99 0\n-3 -9 -11 -20 -21 -22 -44 -45 -50 -55 -74 -78 -89 -98 -99 0\n-3 -9 -14 -20 -21 -24 -28 -46 -55 -59 -69 -74 -89 -98 -99 0\n-2 -10 -15 -18 -19 -25 -37 -43 -47 -60 -73 -79 -89 -98 -99 0\n-3 -9 -14 -20 -21 -25 -28 -45 -50 -55 -74 -78 -89 -98 -99 0\n-6 -9 -10 -19 -21 -22 -35 -42 -55 -71 -73 -78 -87 -100 -101 0\n-6 -9 -10 -19 -21 -23 -26 -42 -60 -71 -73 -78 -84 -100 -101 0\n-11 -14 -15 -18 -20 -22 -36 -42 -53 -54 -59 -74 -88 -100 -101 0\n-11 -14 -15 -18 -20 -23 -27 -42 -53 -54 -59 -79 -85 -100 -101 0\n-3 -7 -17 -20 -21 -22 -43 -46 -53 -59 -69 -73 -91 -98 -99 0\n-2 -13 -16 -18 -19 -23 -43 -46 -47 -59 -71 -73 -95 -98 -99 0\n-3 -12 -16 -20 -21 -22 -44 -45 -50 -54 -71 -78 -91 -98 -99 0\n-5 -6 -9 -10 -12 -25 -28 -35 -55 -79 -81 -85 -87 -100 -101 0\n-4 -6 -9 -10 -13 -25 -26 -37 -60 -74 -81 -84 -88 -100 -101 0\n-5 -7 -11 -14 -15 -24 -28 -36 -60 -62 -74 -84 -88 -100 -101 0\n-4 -8 -11 -14 -15 -24 -27 -37 -55 -62 -79 -85 -87 -100 -101 0\n-3 -6 -9 -10 -14 -25 -26 -42 -60 -74 -78 -84 -88 -100 -101 0\n-2 -10 -11 -14 -15 -24 -36 -42 -54 -60 -74 -84 -88 -100 -101 0\n-3 -9 -11 -14 -15 -24 -27 -42 -55 -59 -79 -85 -87 -100 -101 0\n-2 -6 -18 -19 -21 -23 -44 -45 -54 -60 -66 -78 -89 -98 -99 0\n-3 -6 -19 -20 -21 -22 -43 -46 -55 -59 -69 -73 -89 -98 -99 0\n-2 -11 -18 -19 -20 -23 -43 -46 -47 -59 -73 -79 -89 -98 -99 0\n-3 -11 -18 -20 -21 -22 -44 -45 -50 -54 -74 -78 -89 -98 -99 0\n-3 -8 -12 -18 -19 -22 -44 -45 -53 -54 -71 -78 -95 -98 -99 0\n-2 -8 -12 -20 -21 -23 -44 -45 -53 -54 -71 -78 -91 -98 -99 0\n-3 -7 -13 -18 -19 -22 -43 -46 -53 -59 -71 -73 -95 -98 -99 0\n-6 -7 -13 -14 -15 -25 -28 -37 -60 -62 -74 -84 -88 -100 -101 0\n-6 -8 -12 -14 -15 -25 -28 -37 -55 -62 -79 -85 -87 -100 -101 0\n-8 -9 -10 -11 -12 -24 -28 -37 -55 -79 -81 -85 -87 -100 -101 0\n-7 -9 -10 -11 -13 -24 -28 -37 -60 -74 -81 -84 -88 -100 -101 0\n-3 -7 -17 -18 -19 -22 -43 -46 -53 -59 -69 -73 -95 -98 -99 0\n-2 -13 -16 -20 -21 -23 -43 -46 -47 -59 -71 -73 -91 -98 -99 0\n-3 -12 -16 -18 -19 -22 -44 -45 -50 -54 -71 -78 -95 -98 -99 0\n-5 -6 -12 -14 -15 -25 -28 -35 -55 -62 -79 -85 -87 -100 -101 0\n-4 -6 -13 -14 -15 -25 -26 -37 -60 -62 -74 -84 -88 -100 -101 0\n-5 -7 -9 -10 -11 -24 -28 -36 -60 -74 -81 -84 -88 -100 -101 0\n-4 -8 -9 -10 -11 -24 -27 -37 -55 -79 -81 -85 -87 -100 -101 0\n-5 -7 -15 -18 -19 -22 -36 -43 -53 -59 -71 -73 -95 -98 -99 0\n-4 -9 -13 -20 -21 -23 -26 -46 -53 -59 -71 -73 -91 -98 -99 0\n-5 -10 -12 -18 -19 -22 -35 -44 -53 -54 -71 -78 -95 -98 -99 0\n-12 -14 -15 -16 -20 -25 -28 -37 -50 -55 -62 -79 -85 -100 -101 0\n-13 -14 -15 -16 -18 -25 -28 -37 -47 -60 -62 -74 -88 -100 -101 0\n-7 -9 -10 -17 -21 -24 -28 -37 -60 -69 -74 -81 -84 -100 -101 0\n-8 -9 -10 -17 -19 -24 -28 -37 -55 -66 -79 -81 -87 -100 -101 0\n-5 -10 -14 -16 -21 -23 -27 -43 -47 -60 -71 -78 -91 -98 -99 0\n-4 -10 -14 -17 -18 -22 -35 -46 -53 -54 -69 -74 -95 -98 -99 0\n-5 -9 -15 -17 -20 -23 -26 -44 -53 -59 -66 -79 -91 -98 -99 0\n-4 -10 -16 -18 -21 -24 -27 -37 -54 -60 -69 -81 -85 -100 -101 0\n-5 -9 -16 -19 -20 -24 -28 -36 -55 -59 -66 -81 -88 -100 -101 0\n-4 -15 -17 -19 -20 -25 -26 -37 -50 -62 -73 -79 -84 -100 -101 0\n-5 -14 -17 -18 -21 -25 -28 -35 -47 -62 -74 -78 -87 -100 -101 0\n-3 -9 -14 -16 -18 -25 -28 -45 -47 -60 -74 -78 -88 -96 -97 0\n-2 -10 -15 -17 -21 -24 -37 -44 -54 -60 -69 -74 -84 -96 -97 0\n-3 -9 -14 -17 -19 -24 -28 -46 -55 -59 -66 -79 -87 -96 -97 0\n-4 -6 -14 -19 -21 -23 -27 -45 -54 -60 -71 -78 -84 -96 -97 0\n-5 -6 -15 -19 -21 -22 -36 -43 -55 -59 -71 -73 -87 -96 -97 0\n-4 -9 -11 -18 -20 -23 -26 -46 -53 -59 -73 -79 -85 -96 -97 0\n-5 -10 -11 -18 -20 -22 -35 -44 -53 -54 -74 -78 -88 -96 -97 0\n-3 -6 -7 -9 -14 -25 -28 -45 -60 -74 -78 -84 -88 -96 -97 0\n-2 -10 -11 -13 -15 -24 -37 -44 -54 -60 -74 -84 -88 -96 -97 0\n-3 -9 -11 -12 -14 -24 -28 -46 -55 -59 -79 -85 -87 -96 -97 0\n-2 -6 -12 -19 -21 -23 -44 -45 -54 -60 -71 -78 -84 -96 -97 0\n-3 -6 -13 -19 -21 -22 -43 -46 -55 -59 -71 -73 -87 -96 -97 0\n-2 -7 -11 -18 -20 -23 -43 -46 -53 -59 -73 -79 -85 -96 -97 0\n-3 -8 -11 -18 -20 -22 -44 -45 -53 -54 -74 -78 -88 -96 -97 0\n-3 -4 -5 -6 -19 -25 -26 -60 -62 -73 -78 -84 -88 -100 -101 0\n-2 -4 -5 -11 -20 -24 -36 -54 -59 -74 -81 -84 -88 -100 -101 0\n-3 -4 -5 -11 -18 -24 -27 -54 -59 -79 -81 -85 -87 -100 -101 0\n-2 -6 -15 -16 -17 -23 -44 -45 -54 -60 -66 -79 -91 -98 -99 0\n-3 -6 -14 -16 -17 -22 -43 -46 -55 -59 -69 -74 -95 -98 -99 0\n-2 -10 -11 -16 -17 -23 -43 -46 -47 -60 -73 -79 -91 -98 -99 0\n-3 -9 -11 -16 -17 -22 -44 -45 -50 -55 -74 -78 -95 -98 -99 0\n-3 -4 -9 -16 -19 -22 -45 -50 -55 -71 -73 -78 -95 -98 -99 0\n-2 -5 -15 -17 -20 -23 -44 -53 -54 -59 -66 -79 -91 -98 -99 0\n-3 -4 -14 -17 -18 -22 -46 -53 -54 -59 -69 -74 -95 -98 -99 0\n-4 -6 -15 -17 -19 -25 -26 -37 -60 -62 -73 -79 -84 -100 -101 0\n-5 -6 -14 -17 -21 -25 -28 -35 -55 -62 -74 -78 -87 -100 -101 0\n-4 -10 -11 -16 -18 -24 -27 -37 -54 -60 -79 -81 -85 -100 -101 0\n-5 -9 -11 -16 -20 -24 -28 -36 -55 -59 -74 -81 -88 -100 -101 0\n-3 -7 -14 -17 -18 -22 -43 -46 -53 -59 -69 -74 -95 -98 -99 0\n-2 -10 -13 -16 -21 -23 -43 -46 -47 -60 -71 -73 -91 -98 -99 0\n-3 -9 -12 -16 -19 -22 -44 -45 -50 -55 -71 -78 -95 -98 -99 0\n-5 -6 -12 -14 -21 -25 -28 -35 -55 -62 -78 -85 -87 -100 -101 0\n-4 -6 -13 -15 -19 -25 -26 -37 -60 -62 -73 -84 -88 -100 -101 0\n-5 -7 -9 -11 -20 -24 -28 -36 -59 -74 -81 -84 -88 -100 -101 0\n-4 -8 -10 -11 -18 -24 -27 -37 -54 -79 -81 -85 -87 -100 -101 0\n-2 -3 -5 -10 -16 -25 -43 -47 -60 -73 -78 -88 -91 -98 -99 0\n-2 -3 -4 -14 -17 -24 -46 -54 -59 -69 -74 -84 -95 -98 -99 0\n-2 -3 -5 -15 -17 -24 -44 -54 -59 -66 -79 -87 -91 -98 -99 0\n-4 -6 -11 -16 -18 -23 -27 -45 -54 -60 -79 -81 -85 -100 -101 0\n-5 -6 -11 -16 -20 -22 -36 -43 -55 -59 -74 -81 -88 -100 -101 0\n-4 -6 -11 -17 -19 -23 -26 -46 -60 -62 -73 -79 -84 -100 -101 0\n-5 -6 -11 -17 -21 -22 -35 -44 -55 -62 -74 -78 -87 -100 -101 0\n-2 -3 -5 -10 -16 -25 -43 -50 -55 -73 -78 -85 -95 -98 -99 0\n-2 -3 -4 -14 -17 -24 -46 -54 -59 -66 -79 -87 -91 -98 -99 0\n-2 -3 -5 -15 -17 -24 -44 -54 -59 -69 -74 -84 -95 -98 -99 0\n-4 -6 -11 -16 -18 -23 -26 -46 -60 -62 -73 -79 -85 -100 -101 0\n-5 -6 -11 -16 -20 -22 -35 -44 -55 -62 -74 -78 -88 -100 -101 0\n-4 -6 -11 -17 -19 -23 -27 -45 -54 -60 -79 -81 -84 -100 -101 0\n-5 -6 -11 -17 -21 -22 -36 -43 -55 -59 -74 -81 -87 -100 -101 0\n-3 -7 -9 -14 -17 -24 -28 -46 -59 -66 -79 -87 -91 -98 -99 0\n-2 -10 -13 -15 -16 -25 -37 -43 -50 -55 -73 -85 -95 -98 -99 0\n-3 -9 -12 -14 -16 -25 -28 -45 -47 -60 -78 -88 -91 -98 -99 0\n-5 -6 -12 -19 -21 -22 -36 -43 -55 -59 -71 -81 -87 -100 -101 0\n-4 -6 -13 -19 -21 -23 -27 -45 -54 -60 -71 -81 -84 -100 -101 0\n-5 -7 -11 -18 -20 -22 -35 -44 -53 -62 -74 -78 -88 -100 -101 0\n-4 -8 -11 -18 -20 -23 -26 -46 -53 -62 -73 -79 -85 -100 -101 0\n-3 -7 -9 -14 -17 -24 -28 -46 -59 -69 -74 -84 -95 -98 -99 0\n-2 -10 -13 -15 -16 -25 -37 -43 -47 -60 -73 -88 -91 -98 -99 0\n-3 -9 -12 -14 -16 -25 -28 -45 -50 -55 -78 -85 -95 -98 -99 0\n-5 -6 -12 -19 -21 -22 -35 -44 -55 -62 -71 -78 -87 -100 -101 0\n-4 -6 -13 -19 -21 -23 -26 -46 -60 -62 -71 -73 -84 -100 -101 0\n-5 -7 -11 -18 -20 -22 -36 -43 -53 -59 -74 -81 -88 -100 -101 0\n-4 -8 -11 -18 -20 -23 -27 -45 -53 -54 -79 -81 -85 -100 -101 0\n-3 -7 -9 -14 -17 -25 -28 -45 -50 -74 -78 -84 -95 -98 -99 0\n-2 -10 -13 -15 -16 -24 -37 -44 -54 -60 -66 -88 -91 -98 -99 0\n-3 -9 -12 -14 -16 -24 -28 -46 -55 -59 -69 -85 -95 -98 -99 0\n-5 -6 -12 -19 -21 -23 -26 -44 -60 -62 -71 -78 -84 -100 -101 0\n-4 -6 -13 -19 -21 -22 -35 -46 -55 -62 -71 -73 -87 -100 -101 0\n-5 -7 -11 -18 -20 -23 -27 -43 -53 -59 -79 -81 -85 -100 -101 0\n-4 -8 -11 -18 -20 -22 -36 -45 -53 -54 -74 -81 -88 -100 -101 0\n-3 -9 -14 -16 -17 -24 -28 -46 -55 -59 -69 -74 -95 -98 -99 0\n-2 -10 -15 -16 -17 -25 -37 -43 -47 -60 -73 -79 -91 -98 -99 0\n-3 -9 -14 -16 -17 -25 -28 -45 -50 -55 -74 -78 -95 -98 -99 0\n-4 -5 -6 -19 -21 -22 -35 -55 -62 -71 -73 -78 -87 -100 -101 0\n-4 -5 -6 -19 -21 -23 -26 -60 -62 -71 -73 -78 -84 -100 -101 0\n-4 -5 -11 -18 -20 -22 -36 -53 -54 -59 -74 -81 -88 -100 -101 0\n-4 -5 -11 -18 -20 -23 -27 -53 -54 -59 -79 -81 -85 -100 -101 0\n-3 -6 -7 -9 -14 -25 -28 -45 -60 -74 -78 -84 -88 -98 -99 0\n-2 -10 -11 -13 -15 -24 -37 -44 -54 -60 -74 -84 -88 -98 -99 0\n-3 -9 -11 -12 -14 -24 -28 -46 -55 -59 -79 -85 -87 -98 -99 0\n-2 -6 -12 -19 -21 -23 -44 -45 -54 -60 -71 -78 -84 -100 -101 0\n-3 -6 -13 -19 -21 -22 -43 -46 -55 -59 -71 -73 -87 -100 -101 0\n-2 -7 -11 -18 -20 -23 -43 -46 -53 -59 -73 -79 -85 -100 -101 0\n-3 -8 -11 -18 -20 -22 -44 -45 -53 -54 -74 -78 -88 -100 -101 0\n-3 -9 -14 -16 -18 -25 -28 -45 -47 -60 -74 -78 -88 -98 -99 0\n-2 -10 -15 -17 -21 -24 -37 -44 -54 -60 -69 -74 -84 -98 -99 0\n-3 -9 -14 -17 -19 -24 -28 -46 -55 -59 -66 -79 -87 -98 -99 0\n-4 -6 -14 -19 -21 -23 -27 -45 -54 -60 -71 -78 -84 -100 -101 0\n-5 -6 -15 -19 -21 -22 -36 -43 -55 -59 -71 -73 -87 -100 -101 0\n-4 -9 -11 -18 -20 -23 -26 -46 -53 -59 -73 -79 -85 -100 -101 0\n-5 -10 -11 -18 -20 -22 -35 -44 -53 -54 -74 -78 -88 -100 -101 0\n-3 -9 -14 -19 -20 -24 -28 -46 -55 -59 -66 -79 -89 -98 -99 0\n-2 -10 -15 -19 -20 -25 -37 -43 -50 -55 -73 -79 -89 -98 -99 0\n-3 -9 -14 -18 -21 -25 -28 -45 -47 -60 -74 -78 -89 -98 -99 0\n-6 -9 -15 -19 -21 -22 -36 -42 -55 -59 -71 -73 -87 -100 -101 0\n-6 -10 -14 -19 -21 -23 -27 -42 -54 -60 -71 -78 -84 -100 -101 0\n-10 -11 -14 -18 -20 -22 -35 -42 -53 -54 -74 -78 -88 -100 -101 0\n-9 -11 -15 -18 -20 -23 -26 -42 -53 -59 -73 -79 -85 -100 -101 0\n-3 -9 -14 -16 -18 -25 -28 -45 -47 -60 -74 -78 -88 -100 -101 0\n-2 -10 -15 -17 -21 -24 -37 -44 -54 -60 -69 -74 -84 -100 -101 0\n-3 -9 -14 -17 -19 -24 -28 -46 -55 -59 -66 -79 -87 -100 -101 0\n-4 -6 -14 -19 -21 -23 -27 -45 -54 -60 -71 -78 -84 -98 -99 0\n-5 -6 -15 -19 -21 -22 -36 -43 -55 -59 -71 -73 -87 -98 -99 0\n-4 -9 -11 -18 -20 -23 -26 -46 -53 -59 -73 -79 -85 -98 -99 0\n-5 -10 -11 -18 -20 -22 -35 -44 -53 -54 -74 -78 -88 -98 -99 0\n-3 -6 -7 -9 -14 -25 -28 -45 -60 -74 -78 -84 -88 -100 -101 0\n-2 -10 -11 -13 -15 -24 -37 -44 -54 -60 -74 -84 -88 -100 -101 0\n-3 -9 -11 -12 -14 -24 -28 -46 -55 -59 -79 -85 -87 -100 -101 0\n-2 -6 -12 -19 -21 -23 -44 -45 -54 -60 -71 -78 -84 -98 -99 0\n-3 -6 -13 -19 -21 -22 -43 -46 -55 -59 -71 -73 -87 -98 -99 0\n-2 -7 -11 -18 -20 -23 -43 -46 -53 -59 -73 -79 -85 -98 -99 0\n-3 -8 -11 -18 -20 -22 -44 -45 -53 -54 -74 -78 -88 -98 -99 0\n-3 -6 -9 -15 -18 -25 -26 -42 -59 -73 -79 -85 -87 -100 -101 0\n-2 -9 -11 -15 -21 -24 -36 -42 -55 -59 -73 -85 -87 -100 -101 0\n-3 -10 -11 -14 -19 -24 -27 -42 -54 -60 -78 -84 -88 -100 -101 0\n-2 -6 -14 -19 -20 -23 -43 -46 -55 -59 -66 -79 -89 -98 -99 0\n-3 -6 -15 -18 -21 -22 -44 -45 -54 -60 -69 -74 -89 -98 -99 0\n-2 -9 -11 -18 -21 -23 -44 -45 -47 -60 -74 -78 -89 -98 -99 0\n-3 -10 -11 -19 -20 -22 -43 -46 -50 -55 -73 -79 -89 -98 -99 0\n-3 -10 -14 -19 -21 -24 -27 -42 -54 -60 -71 -78 -84 -100 -101 0\n-2 -10 -14 -18 -20 -25 -35 -42 -53 -54 -74 -78 -88 -100 -101 0\n-3 -9 -15 -18 -20 -25 -26 -42 -53 -59 -73 -79 -85 -100 -101 0\n-6 -10 -15 -18 -21 -22 -37 -44 -54 -60 -69 -74 -89 -98 -99 0\n-6 -9 -14 -19 -20 -23 -28 -46 -55 -59 -66 -79 -89 -98 -99 0\n-10 -11 -15 -19 -20 -22 -37 -43 -50 -55 -73 -79 -89 -98 -99 0\n-9 -11 -14 -18 -21 -23 -28 -45 -47 -60 -74 -78 -89 -98 -99 0\n-3 -5 -10 -16 -19 -22 -43 -50 -55 -71 -73 -78 -95 -98 -99 0\n-2 -4 -14 -17 -20 -23 -46 -53 -54 -59 -66 -79 -91 -98 -99 0\n-3 -5 -15 -17 -18 -22 -44 -53 -54 -59 -69 -74 -95 -98 -99 0\n-4 -6 -15 -16 -18 -25 -26 -37 -60 -62 -73 -79 -85 -100 -101 0\n-5 -6 -14 -16 -20 -25 -28 -35 -55 -62 -74 -78 -88 -100 -101 0\n-4 -10 -11 -17 -19 -24 -27 -37 -54 -60 -79 -81 -84 -100 -101 0\n-5 -9 -11 -17 -21 -24 -28 -36 -55 -59 -74 -81 -87 -100 -101 0\n-3 -8 -15 -17 -18 -22 -44 -45 -53 -54 -69 -74 -95 -98 -99 0\n-2 -9 -12 -16 -21 -23 -44 -45 -47 -60 -71 -78 -91 -98 -99 0\n-3 -10 -13 -16 -19 -22 -43 -46 -50 -55 -71 -73 -95 -98 -99 0\n-5 -6 -7 -14 -20 -25 -28 -35 -62 -74 -78 -84 -88 -100 -101 0\n-4 -6 -8 -15 -18 -25 -26 -37 -62 -73 -79 -85 -87 -100 -101 0\n-5 -9 -11 -12 -21 -24 -28 -36 -55 -59 -81 -85 -87 -100 -101 0\n-4 -10 -11 -13 -19 -24 -27 -37 -54 -60 -81 -84 -88 -100 -101 0\n-5 -10 -15 -16 -19 -22 -36 -43 -50 -55 -71 -73 -95 -98 -99 0\n-4 -9 -14 -17 -20 -23 -26 -46 -53 -59 -66 -79 -91 -98 -99 0\n-5 -10 -15 -17 -18 -22 -35 -44 -53 -54 -69 -74 -95 -98 -99 0\n-4 -15 -16 -18 -20 -25 -26 -37 -50 -62 -73 -79 -85 -100 -101 0\n-5 -14 -16 -18 -20 -25 -28 -35 -47 -62 -74 -78 -88 -100 -101 0\n-4 -10 -17 -19 -21 -24 -27 -37 -54 -60 -69 -81 -84 -100 -101 0\n-5 -9 -17 -19 -21 -24 -28 -36 -55 -59 -66 -81 -87 -100 -101 0\n-5 -7 -14 -18 -20 -25 -28 -35 -53 -62 -74 -78 -88 -100 -101 0\n-4 -10 -13 -19 -21 -24 -27 -37 -54 -60 -71 -81 -84 -100 -101 0\n-5 -9 -12 -19 -21 -24 -28 -36 -55 -59 -71 -81 -87 -100 -101 0\n-9 -12 -14 -16 -21 -23 -28 -45 -47 -60 -71 -78 -91 -98 -99 0\n-10 -13 -15 -16 -19 -22 -37 -43 -50 -55 -71 -73 -95 -98 -99 0\n-7 -9 -14 -17 -20 -23 -28 -46 -53 -59 -66 -79 -91 -98 -99 0\n-8 -10 -15 -17 -18 -22 -37 -44 -53 -54 -69 -74 -95 -98 -99 0\n-3 -7 -14 -17 -21 -24 -28 -46 -60 -62 -69 -74 -84 -100 -101 0\n-2 -10 -13 -16 -18 -25 -37 -43 -47 -60 -74 -81 -88 -100 -101 0\n-3 -9 -12 -16 -20 -25 -28 -45 -50 -55 -79 -81 -85 -100 -101 0\n-5 -6 -10 -12 -21 -22 -35 -44 -54 -71 -78 -87 -91 -98 -99 0\n-4 -6 -9 -13 -19 -23 -26 -46 -59 -71 -73 -84 -95 -98 -99 0\n-5 -7 -11 -15 -20 -22 -36 -43 -53 -59 -73 -88 -91 -98 -99 0\n-4 -8 -11 -14 -18 -23 -27 -45 -53 -54 -78 -85 -95 -98 -99 0\n-3 -6 -8 -9 -12 -25 -28 -45 -55 -79 -81 -85 -87 -100 -101 0\n-2 -8 -11 -12 -15 -24 -37 -44 -55 -62 -79 -85 -87 -100 -101 0\n-3 -7 -11 -13 -14 -24 -28 -46 -60 -62 -74 -84 -88 -100 -101 0\n-2 -6 -7 -13 -19 -23 -43 -46 -59 -71 -73 -84 -95 -98 -99 0\n-3 -6 -8 -12 -21 -22 -44 -45 -54 -71 -78 -87 -91 -98 -99 0\n-2 -8 -11 -12 -18 -23 -44 -45 -53 -54 -78 -85 -95 -98 -99 0\n-3 -7 -11 -13 -20 -22 -43 -46 -53 -59 -73 -88 -91 -98 -99 0\n-3 -8 -14 -17 -19 -24 -28 -46 -55 -62 -66 -79 -87 -100 -101 0\n-2 -10 -12 -16 -20 -25 -37 -43 -50 -55 -79 -81 -85 -100 -101 0\n-3 -9 -13 -16 -18 -25 -28 -45 -47 -60 -74 -81 -88 -100 -101 0\n-5 -6 -7 -15 -21 -22 -36 -43 -59 -71 -73 -87 -91 -98 -99 0\n-4 -6 -8 -14 -19 -23 -27 -45 -54 -71 -78 -84 -95 -98 -99 0\n-5 -10 -11 -12 -20 -22 -35 -44 -53 -54 -78 -88 -91 -98 -99 0\n-4 -9 -11 -13 -18 -23 -26 -46 -53 -59 -73 -85 -95 -98 -99 0\n-3 -6 -7 -9 -13 -25 -28 -45 -60 -74 -81 -84 -88 -100 -101 0\n-2 -7 -11 -13 -15 -24 -37 -44 -60 -62 -74 -84 -88 -100 -101 0\n-3 -8 -11 -12 -14 -24 -28 -46 -55 -62 -79 -85 -87 -100 -101 0\n-2 -6 -8 -12 -19 -23 -44 -45 -54 -71 -78 -84 -95 -98 -99 0\n-3 -6 -7 -13 -21 -22 -43 -46 -59 -71 -73 -87 -91 -98 -99 0\n-2 -7 -11 -13 -18 -23 -43 -46 -53 -59 -73 -85 -95 -98 -99 0\n-3 -8 -11 -12 -20 -22 -44 -45 -53 -54 -78 -88 -91 -98 -99 0\n-1 -3 -4 -9 -18 -26 -46 -53 -59 -69 -73 -85 -95 -98 -99 0\n-1 -2 -5 -15 -21 -36 -43 -47 -59 -71 -73 -87 -91 -98 -99 0\n-1 -3 -4 -14 -19 -27 -45 -50 -54 -71 -78 -84 -95 -98 -99 0\n-1 -6 -14 -17 -19 -28 -35 -46 -55 -62 -66 -79 -87 -100 -101 0\n-1 -6 -15 -17 -21 -26 -37 -44 -60 -62 -69 -74 -84 -100 -101 0\n-1 -9 -11 -16 -18 -28 -36 -45 -47 -60 -74 -81 -88 -100 -101 0\n-1 -10 -11 -16 -20 -27 -37 -43 -50 -55 -79 -81 -85 -100 -101 0\n-1 -2 -3 -8 -20 -44 -45 -53 -54 -66 -78 -88 -91 -98 -99 0\n-1 -2 -3 -12 -19 -44 -45 -50 -54 -71 -78 -84 -95 -98 -99 0\n-1 -2 -3 -13 -21 -43 -46 -47 -59 -71 -73 -87 -91 -98 -99 0\n-1 -6 -7 -9 -11 -28 -36 -45 -60 -74 -81 -84 -88 -100 -101 0\n-1 -6 -8 -10 -11 -27 -37 -43 -55 -79 -81 -85 -87 -100 -101 0\n-1 -6 -11 -12 -14 -28 -35 -46 -55 -62 -79 -85 -87 -100 -101 0\n-1 -6 -11 -13 -15 -26 -37 -44 -60 -62 -74 -84 -88 -100 -101 0\n-2 -3 -5 -6 -15 -25 -43 -55 -59 -73 -79 -85 -87 -96 -97 0\n-2 -3 -4 -9 -11 -24 -46 -55 -59 -73 -79 -85 -87 -96 -97 0\n-2 -3 -5 -10 -11 -24 -44 -54 -60 -74 -78 -84 -88 -96 -97 0\n-2 -6 -11 -16 -20 -23 -43 -46 -55 -59 -73 -79 -85 -96 -97 0\n-3 -6 -11 -16 -18 -22 -44 -45 -54 -60 -74 -78 -88 -96 -97 0\n-2 -6 -11 -17 -21 -23 -44 -45 -54 -60 -74 -78 -84 -96 -97 0\n-3 -6 -11 -17 -19 -22 -43 -46 -55 -59 -73 -79 -87 -96 -97 0\n-2 -3 -5 -6 -15 -25 -43 -55 -59 -73 -79 -85 -87 -98 -99 0\n-2 -3 -4 -9 -11 -24 -46 -55 -59 -73 -79 -85 -87 -98 -99 0\n-2 -3 -5 -10 -11 -24 -44 -54 -60 -74 -78 -84 -88 -98 -99 0\n-2 -6 -11 -16 -20 -23 -43 -46 -55 -59 -73 -79 -85 -100 -101 0\n-3 -6 -11 -16 -18 -22 -44 -45 -54 -60 -74 -78 -88 -100 -101 0\n-2 -6 -11 -17 -21 -23 -44 -45 -54 -60 -74 -78 -84 -100 -101 0\n-3 -6 -11 -17 -19 -22 -43 -46 -55 -59 -73 -79 -87 -100 -101 0\n-2 -3 -5 -10 -16 -24 -44 -54 -60 -66 -78 -88 -91 -98 -99 0\n-2 -3 -4 -14 -17 -25 -45 -50 -54 -74 -78 -84 -95 -98 -99 0\n-2 -3 -5 -15 -17 -25 -43 -47 -59 -73 -79 -87 -91 -98 -99 0\n-4 -6 -11 -16 -18 -22 -36 -45 -54 -60 -74 -81 -88 -100 -101 0\n-5 -6 -11 -16 -20 -23 -27 -43 -55 -59 -79 -81 -85 -100 -101 0\n-4 -6 -11 -17 -19 -22 -35 -46 -55 -62 -73 -79 -87 -100 -101 0\n-5 -6 -11 -17 -21 -23 -26 -44 -60 -62 -74 -78 -84 -100 -101 0\n-3 -5 -9 -17 -19 -24 -28 -55 -59 -66 -79 -81 -87 -100 -101 0\n-2 -4 -15 -16 -20 -25 -37 -50 -55 -62 -73 -79 -85 -100 -101 0\n-3 -5 -14 -16 -18 -25 -28 -47 -60 -62 -74 -78 -88 -100 -101 0\n-5 -6 -15 -16 -19 -22 -36 -43 -55 -59 -71 -73 -95 -98 -99 0\n-4 -6 -14 -16 -21 -23 -27 -45 -54 -60 -71 -78 -91 -98 -99 0\n-5 -10 -11 -17 -18 -22 -35 -44 -53 -54 -74 -78 -95 -98 -99 0\n-4 -9 -11 -17 -20 -23 -26 -46 -53 -59 -73 -79 -91 -98 -99 0\n-3 -5 -6 -9 -12 -25 -28 -55 -59 -79 -81 -85 -87 -100 -101 0\n-2 -4 -8 -11 -15 -24 -37 -55 -62 -73 -79 -85 -87 -100 -101 0\n-3 -5 -7 -11 -14 -24 -28 -60 -62 -74 -78 -84 -88 -100 -101 0\n-2 -6 -13 -16 -19 -23 -43 -46 -55 -59 -71 -73 -95 -98 -99 0\n-3 -6 -12 -16 -21 -22 -44 -45 -54 -60 -71 -78 -91 -98 -99 0\n-2 -8 -11 -17 -18 -23 -44 -45 -53 -54 -74 -78 -95 -98 -99 0\n-3 -7 -11 -17 -20 -22 -43 -46 -53 -59 -73 -79 -91 -98 -99 0\n-2 -3 -6 -10 -14 -25 -42 -54 -60 -74 -78 -84 -88 -100 -101 0\n-2 -3 -10 -11 -14 -24 -42 -54 -60 -74 -78 -84 -88 -100 -101 0\n-2 -3 -9 -11 -15 -24 -42 -55 -59 -73 -79 -85 -87 -100 -101 0\n-2 -6 -11 -18 -21 -23 -44 -45 -54 -60 -74 -78 -89 -98 -99 0\n-3 -6 -11 -19 -20 -22 -43 -46 -55 -59 -73 -79 -89 -98 -99 0\n-2 -6 -11 -19 -20 -23 -43 -46 -55 -59 -73 -79 -89 -98 -99 0\n-3 -6 -11 -18 -21 -22 -44 -45 -54 -60 -74 -78 -89 -98 -99 0\n-2 -3 -5 -6 -15 -25 -43 -55 -59 -73 -79 -85 -87 -100 -101 0\n-2 -3 -4 -9 -11 -24 -46 -55 -59 -73 -79 -85 -87 -100 -101 0\n-2 -3 -5 -10 -11 -24 -44 -54 -60 -74 -78 -84 -88 -100 -101 0\n-2 -6 -11 -16 -20 -23 -43 -46 -55 -59 -73 -79 -85 -98 -99 0\n-3 -6 -11 -16 -18 -22 -44 -45 -54 -60 -74 -78 -88 -98 -99 0\n-2 -6 -11 -17 -21 -23 -44 -45 -54 -60 -74 -78 -84 -98 -99 0\n-3 -6 -11 -17 -19 -22 -43 -46 -55 -59 -73 -79 -87 -98 -99 0\n-3 -4 -5 -6 -14 -25 -26 -60 -62 -74 -78 -84 -88 -100 -101 0\n-2 -4 -5 -10 -11 -24 -36 -54 -60 -74 -81 -84 -88 -100 -101 0\n-3 -4 -5 -9 -11 -24 -27 -55 -59 -79 -81 -85 -87 -100 -101 0\n-2 -6 -16 -17 -21 -23 -44 -45 -54 -60 -66 -78 -91 -98 -99 0\n-3 -6 -16 -17 -19 -22 -43 -46 -55 -59 -69 -73 -95 -98 -99 0\n-2 -11 -16 -17 -20 -23 -43 -46 -47 -59 -73 -79 -91 -98 -99 0\n-3 -11 -16 -17 -18 -22 -44 -45 -50 -54 -74 -78 -95 -98 -99 0\n-3 -5 -6 -7 -14 -25 -28 -60 -62 -74 -78 -84 -88 -100 -101 0\n-2 -4 -10 -11 -13 -24 -37 -54 -60 -74 -81 -84 -88 -100 -101 0\n-3 -5 -9 -11 -12 -24 -28 -55 -59 -79 -81 -85 -87 -100 -101 0\n-2 -6 -12 -16 -21 -23 -44 -45 -54 -60 -71 -78 -91 -98 -99 0\n-3 -6 -13 -16 -19 -22 -43 -46 -55 -59 -71 -73 -95 -98 -99 0\n-2 -7 -11 -17 -20 -23 -43 -46 -53 -59 -73 -79 -91 -98 -99 0\n-3 -8 -11 -17 -18 -22 -44 -45 -53 -54 -74 -78 -95 -98 -99 0\n-1 -2 -3 -6 -11 -44 -45 -54 -60 -74 -78 -84 -88 -96 -97 0\n-1 -2 -3 -6 -11 -44 -45 -54 -60 -74 -78 -84 -88 -98 -99 0\n-1 -2 -3 -6 -11 -44 -45 -54 -60 -74 -78 -84 -88 -100 -101 0\n-1 -2 -3 -6 -11 -43 -46 -55 -59 -73 -79 -85 -87 -100 -101 0\n-1 -2 -3 -6 -16 -44 -45 -54 -60 -66 -78 -88 -91 -98 -99 0\n-1 -2 -3 -11 -17 -44 -45 -50 -54 -74 -78 -84 -95 -98 -99 0\n-1 -2 -3 -11 -17 -43 -46 -47 -59 -73 -79 -87 -91 -98 -99 0\n-1 -2 -4 -6 -11 -36 -45 -54 -60 -74 -81 -84 -88 -100 -101 0\n-1 -3 -5 -6 -11 -27 -43 -55 -59 -79 -81 -85 -87 -100 -101 0\n-1 -2 -4 -6 -11 -35 -46 -55 -62 -73 -79 -85 -87 -100 -101 0\n-1 -3 -5 -6 -11 -26 -44 -60 -62 -74 -78 -84 -88 -100 -101 0\n-2 -3 -5 -6 -12 -25 -43 -55 -59 -79 -81 -85 -87 -100 -101 0\n-2 -3 -4 -8 -11 -24 -46 -55 -62 -73 -79 -85 -87 -100 -101 0\n-2 -3 -5 -7 -11 -24 -44 -60 -62 -74 -78 -84 -88 -100 -101 0\n-2 -6 -11 -13 -16 -23 -43 -46 -55 -59 -73 -85 -95 -98 -99 0\n-3 -6 -11 -12 -16 -22 -44 -45 -54 -60 -78 -88 -91 -98 -99 0\n-2 -6 -8 -11 -17 -23 -44 -45 -54 -74 -78 -84 -95 -98 -99 0\n-3 -6 -7 -11 -17 -22 -43 -46 -59 -73 -79 -87 -91 -98 -99 0\n18 19 49 55 58 63 67 74 76 82 84 85 91 93 97 98 99 100 0\n20 21 52 57 60 63 70 75 79 82 87 88 92 95 97 98 99 101 0\n9 10 31 38 43 45 54 59 62 72 77 80 90 94 96 98 100 101 0\n"
  "1245 -175 0 662 656 0\n1246 193 0 753 749 0\n1247 -210 49 52 0 511 775 0\n1248 -213 70 76 0 516 789 0\n1249 -216 92 93 0 521 522 801 0\n1250 18 19 49 55 58 67 74 76 84 85 91 93 97 98 99 100 0 511 516 1242 0\n1251 20 21 52 57 60 70 75 79 87 88 92 95 97 98 99 101 0 511 516 1243 0\n1252 9 10 31 38 43 45 54 59 62 72 77 80 96 98 100 101 0 521 522 1244 0\n1253 221 0 521 522 814 815 813 804 806 765 767 768 762 756 757 758 492 500 504 354 345 352 346 353 344 351 1252 0\n1254 -231 0 1253 843 840 0\n1255 -229 0 1254 835 0\n1256 -225 0 1254 838 0\n1257 -227 0 1255 831 0\n1258 -216 93 0 1257 1249 828 520 800 0\n1259 -57 76 222 0 753 516 81 82 83 84 95 111 159 165 510 671 704 172 185 777 719 737 809 741 812 747 817 750 804 726 761 712 464 667 0\n1260 217 224 0 516 511 823 783 518 780 507 822 819 791 782 804 806 760 761 757 758 457 463 456 462 464 461 455 1250 0\n1261 -228 222 0 1254 837 822 823 819 783 790 791 518 515 1258 802 519 1259 797 825 829 1260 817 813 764 765 767 768 488 492 500 504 792 0\n1262 76 220 -230 0 843 812 810 773 502 770 490 771 494 774 506 784 772 498 809 776 508 813 766 496 841 1261 830 827 799 514 826 803 517 833 512 1248 778 818 821 0\n1263 -76 0 1256 513 791 782 819 824 0\n1264 -67 0 1263 512 0\n1265 -230 0 843 1263 516 511 841 1261 830 826 827 802 798 799 509 514 1262 817 804 806 760 761 762 757 475 482 474 481 483 480 473 1251 0\n1266 -228 0 1265 834 0\n1267 -224 0 1265 836 0\n1268 222 0 1265 842 839 0\n1269 -226 0 1266 830 0\n1270 -214 0 1266 832 0\n1271 -223 0 1267 822 0\n1272 -211 0 1267 823 0\n1273 -216 0 1269 826 0\n1274 -215 0 1269 827 0\n1275 -68 0 1270 793 0\n1276 -72 0 1270 794 0\n1277 -77 0 1270 795 0\n1278 -80 0 1270 796 0\n1279 -213 0 1271 819 0\n1280 -212 0 1271 820 0\n1281 -48 0 1272 779 0\n1282 -58 0 1272 780 0\n1283 -65 0 1272 781 0\n1284 -83 0 1272 783 0\n1285 -92 0 1273 802 0\n1286 -93 0 1273 803 0\n1287 -57 0 1274 798 0\n1288 -75 0 1274 799 0\n1289 -86 0 1274 800 0\n1290 -29 0 1275 487 0\n1291 -31 0 1276 491 0\n1292 -38 0 1277 499 0\n1293 -40 0 1278 503 0\n1294 -70 0 1279 790 0\n1295 -51 0 1280 785 0\n1296 -56 0 1280 786 0\n1297 -61 0 1280 787 0\n1298 -64 0 1280 788 0\n1299 -34 0 1281 497 0\n1300 -49 0 1282 507 0\n1301 -33 0 1283 495 0\n1302 -52 0 1287 509 0\n1303 -30 0 1295 489 0\n1304 -32 0 1296 493 0\n1305 -39 0 1297 501 0\n1306 -41 0 1298 505 0\n1307 -210 0 1300 1302 1247 0\n1308 -208 0 1301 1291 1290 1292 1293 763 0\n1309 -209 0 1306 1304 1303 1305 1299 769 0\n1310 -219 0 1307 1309 808 0\n1311 -220 0 1310 1308 811 0\n1312 218 0 1311 1268 816 0\n1313 206 0 1312 805 0\n1314 207 0 1312 807 0\n1315 141 -59 27 22 47 55 0 511 1282 1281 1300 1291 586 588 577 580 562 572 564 551 569 533 528 537 319 243 343 0\n1316 60 69 87 88 74 84 85 -186 -183 -182 -181 -179 -97 -96 55 0 1282 1263 1287 1289 1295 662 1296 465 548 459 547 193 477 671 549 70 71 623 704 628 1 28 687 105 115 121 372 683 546 136 617 679 619 638 1315 657 645 607 602 599 600 544 543 401 409 0\n1317 153 66 46 36 25 74 -184 81 0 516 1263 607 609 602 596 600 541 543 379 378 692 0\n1318 69 87 88 74 84 85 -186 -184 -183 -182 -181 -179 -97 -96 81 55 95 0 1282 1263 1286 1289 1295 662 1276 465 548 459 547 615 193 1316 92 96 434 704 545 1 6 22 28 621 679 128 136 397 683 550 115 622 687 628 76 638 1317 645 657 586 577 572 568 569 539 537 340 348 0\n1319 -69 74 -182 0 116 133 683 0\n1320 -87 -179 55 0 158 160 671 0\n1321 87 69 95 74 84 85 -186 -184 -183 -182 -181 -179 -97 -96 81 55 0 1318 167 168 683 0\n1322 74 84 85 -186 -184 -183 -182 -181 -179 -97 -96 81 55 95 0 1320 1319 1321 0\n1323 134 43 26 24 60 50 -185 62 0 511 1287 572 574 568 535 539 329 328 698 0\n1324 132 -134 -54 -11 -22 -53 -20 -88 -74 -18 -184 -181 -97 -96 62 0 1298 511 1287 1293 1290 1294 1275 5 163 122 568 571 539 534 287 328 85 327 679 289 126 266 692 978 0\n1325 60 -88 69 -74 84 85 -185 -184 -183 -181 -180 -179 -97 -96 62 55 0 1282 1294 1275 1278 164 125 124 123 122 459 192 472 671 69 70 687 5 9 14 227 675 72 75 536 1323 1324 567 538 45 86 698 25 29 679 128 297 692 971 0\n1326 -22 -16 -60 -88 69 -74 -18 -185 -184 -181 -180 -97 -96 0 1302 1295 1294 1275 96 93 91 164 163 125 124 122 2 5 9 14 221 227 675 75 698 49 59 679 126 266 692 1165 0\n1327 -88 69 -74 84 85 -185 -184 -183 -181 -180 -179 -97 -96 81 62 55 0 1282 1286 1298 1278 1294 1275 125 123 122 459 193 163 1325 91 96 434 1326 687 62 63 76 675 36 41 276 281 698 49 59 679 126 266 692 965 0\n1328 -60 88 69 73 66 27 84 85 87 -186 -184 -183 -181 -180 0 92 96 704 1 6 22 28 687 679 76 128 675 692 41 0\n1329 69 -74 84 85 -186 -185 -184 -183 -181 -180 -179 -97 -96 81 62 55 0 125 123 122 1320 1327 1328 671 70 71 687 704 1 0\n1330 60 -160 -122 78 50 73 66 84 85 -185 -183 -180 -179 -97 -96 62 55 0 1287 662 1292 1291 1297 1320 477 671 549 69 70 624 687 626 9 14 638 675 640 75 658 1323 577 586 589 657 560 645 556 607 554 602 530 599 274 544 416 0\n1331 84 85 -186 -185 -184 -183 -182 -181 -180 -179 -97 -96 81 62 55 95 0 1282 1284 1281 522 1297 193 459 547 1322 122 123 125 1329 108 109 110 130 373 396 546 550 617 619 1330 91 96 679 49 56 692 41 44 675 73 76 698 687 2 0\n1332 -69 -74 -60 -84 85 -185 -184 -181 -180 -97 -96 81 62 95 0 1284 522 1297 1298 1278 1281 1300 125 122 96 91 144 193 108 109 130 373 396 679 49 56 287 294 692 41 44 675 73 243 698 966 0\n1333 -37 -54 69 -74 -60 -84 87 -186 -185 -184 -97 -96 81 62 0 1300 1281 1275 1298 1278 1294 1264 122 144 243 75 73 135 124 92 91 148 28 30 49 56 264 287 294 704 698 7 229 692 973 0\n1334 -24 -78 37 -54 69 -74 -60 -84 87 -186 -184 -97 -96 62 0 1300 1281 1305 1299 1294 1264 1293 1290 1278 128 126 122 144 243 124 92 148 192 3 7 46 214 229 704 692 331 297 1163 0\n1335 -88 -44 -11 25 -6 -45 -78 37 -54 -74 -60 -84 -97 -96 0 1297 1302 1295 1300 1281 126 122 144 243 163 261 220 1224 0\n1336 25 -6 -45 -78 37 -54 69 -74 -60 -84 87 -186 -184 -97 -96 0 1300 1281 1304 1303 1285 1288 128 126 122 144 243 135 92 193 364 692 1335 440 484 704 1166 0\n1337 -54 69 -74 -60 -84 87 -186 -185 -184 -181 -97 -96 81 62 0 1281 1300 1287 1290 1292 1301 1296 1298 125 122 96 92 91 146 144 192 73 75 243 1333 679 1334 698 302 1336 6 39 215 704 409 278 882 0\n1338 -78 -14 -9 -7 -28 69 -74 -60 -84 87 -186 -185 -184 -97 -96 0 1292 1301 1302 1300 41 36 15 122 92 91 146 145 126 127 128 692 6 7 215 223 704 698 972 0\n1339 -74 -60 -84 85 87 -186 -185 -184 -181 -180 -97 -96 81 62 55 95 0 1300 1281 1298 1278 96 91 145 122 125 1332 1337 675 15 36 41 241 276 281 1338 679 30 49 56 698 692 7 0\n1340 -88 74 -182 0 167 168 683 0\n1341 -44 54 -180 0 41 119 675 0\n1342 54 46 36 25 187 0 1246 753 724 750 747 739 723 721 715 1341 692 16 117 675 0\n1343 -27 -45 -54 -71 -21 -78 -23 -19 -60 -84 -97 -96 81 0 1300 1281 516 1263 1301 1293 75 145 146 222 192 378 234 968 0\n1344 85 187 -97 -96 81 62 55 95 0 753 1246 1263 1289 1295 1281 1300 1304 1303 723 719 1320 724 750 747 741 737 736 739 745 733 732 721 716 715 1331 144 145 146 671 91 92 96 1339 465 1319 1340 704 3 6 22 28 222 679 128 136 397 683 1342 73 75 120 698 1343 692 243 362 975 0\n1345 167 -157 -85 87 95 0 1294 1302 1286 618 636 633 621 625 545 623 423 549 433 0\n1346 148 -12 78 81 0 516 1263 1306 1299 599 600 544 543 401 377 0\n1347 -50 -179 55 0 71 92 671 0\n1348 -12 155 -112 78 81 0 541 1346 598 602 614 0\n1349 43 -46 -73 -53 -20 -59 -23 -79 -18 -85 -185 -97 -96 0 1283 1264 1276 1278 120 89 152 153 228 18 3 192 348 698 284 970 0\n1350 -46 -73 27 -53 -20 -59 -23 -79 -85 -185 -97 -96 55 0 1283 1264 1306 1299 511 1282 152 153 228 454 151 150 1349 236 319 977 0\n1351 27 -20 -167 -85 187 -97 -96 81 55 0 1283 1264 753 1246 662 1288 1304 1303 723 719 721 716 724 750 745 732 154 153 683 136 1319 1320 747 741 737 169 1347 704 28 679 96 671 152 228 540 6 132 151 150 736 1315 657 653 1348 357 120 1350 1342 0\n1352 100 55 99 0 1263 516 1288 1276 1296 521 1313 1314 1246 753 1289 1275 483 464 523 526 347 408 755 759 192 193 663 667 708 723 724 719 721 750 715 716 745 747 732 741 736 737 1320 1344 153 154 169 454 683 1319 547 136 615 1345 1347 704 3 18 28 679 89 335 1351 12 16 117 698 675 75 0\n1353 87 -79 -15 -14 -27 -85 -100 55 95 0 662 1301 511 1282 521 1283 1284 1299 1305 1298 1278 1276 1277 1297 1281 1300 1289 1275 543 544 601 603 152 11 369 540 597 611 16 12 454 547 615 151 150 525 1345 653 657 586 588 577 580 560 562 572 564 565 556 558 552 568 533 532 554 529 527 539 322 319 323 530 216 287 280 267 288 222 335 922 0\n1354 -79 78 -27 81 -85 178 -100 55 95 0 1263 516 1297 1298 1305 1299 1246 753 1302 1295 525 54 418 378 117 24 16 12 11 454 152 712 725 369 1353 156 1320 719 718 723 726 715 716 708 750 675 747 75 100 741 663 736 32 50 679 87 260 698 911 0\n1355 78 -27 81 -85 178 -100 55 95 0 753 117 16 12 154 153 712 728 751 1354 683 732 745 744 750 741 724 726 736 708 719 721 715 716 675 75 100 663 32 50 679 87 96 698 671 69 0\n1356 -27 81 -85 178 -100 55 95 0 753 169 154 153 712 728 751 12 16 117 1355 130 136 683 732 745 744 750 741 724 726 736 737 708 719 721 1320 1347 715 704 675 3 18 75 100 698 663 50 0\n1357 -78 27 81 -85 178 55 0 753 169 154 153 712 728 751 126 128 130 136 683 732 745 744 750 739 741 724 726 737 708 719 721 1320 1347 715 704 6 692 43 1341 663 100 0\n1358 -62 -181 -180 50 87 -186 -184 78 27 88 0 100 101 1341 679 28 30 56 704 692 108 0\n1359 79 27 81 -85 178 55 95 0 753 1277 1289 1275 662 1263 1357 454 547 615 618 169 154 153 152 151 150 712 728 751 447 683 550 732 745 744 750 739 741 724 726 737 708 719 721 1320 1347 715 716 1358 663 32 43 57 295 679 544 335 1315 599 549 657 602 624 626 634 649 608 610 605 597 542 540 365 366 692 0\n1360 43 -46 28 -73 -53 -20 -59 -23 -185 62 -79 -18 -85 -100 0 1283 1264 1278 1276 1292 1291 120 89 152 153 228 18 3 525 698 350 274 1054 0\n1361 -46 28 -73 -53 -20 -59 -23 -185 62 -79 27 -85 -100 55 0 1283 1264 1306 1299 511 1282 152 153 228 454 151 150 525 1360 236 319 1047 0\n1362 -59 -199 -179 62 81 -85 178 -100 55 95 0 1289 1275 662 1288 1304 1303 1264 1283 1298 1297 1296 152 153 1356 1359 133 1320 1347 169 737 704 228 540 18 6 3 736 454 547 615 1345 132 1357 154 151 150 525 89 96 335 1315 671 657 653 1348 357 246 120 1361 418 1342 708 663 38 277 698 1062 0\n1363 -199 -179 62 81 -85 178 -100 55 95 0 1246 753 1347 1320 1356 1359 133 132 1357 169 712 737 704 6 28 1362 679 716 721 723 726 708 750 663 747 43 57 739 692 0\n1364 -179 62 81 -85 178 -100 55 95 0 753 1277 1289 1275 1292 1301 511 1282 1356 1359 133 132 1357 454 169 712 728 751 746 740 525 1320 1347 1363 741 738 747 750 724 726 708 721 663 715 716 31 32 38 43 50 57 295 679 692 87 96 335 6 7 215 671 704 735 698 73 318 675 1086 0\n1365 62 81 -85 178 -100 55 95 0 1246 753 1277 1292 1301 1302 1300 511 1282 1356 1359 133 132 1357 454 169 151 712 725 525 1364 672 719 718 723 726 715 716 708 750 663 747 31 32 38 43 50 57 295 739 741 679 692 736 737 87 90 6 7 215 223 698 704 73 318 675 1077 0\n1366 -87 -73 -4 -26 -25 -15 -37 -62 -79 -18 -85 -100 0 522 1277 1284 1283 7 29 101 151 525 336 316 1102 0\n1367 179 -62 -79 78 27 81 -18 -85 188 -100 0 1246 753 1278 1299 1306 1285 1287 1302 101 100 99 98 97 133 132 169 725 525 202 672 674 719 718 726 715 716 750 1341 679 747 28 29 56 294 739 741 692 736 737 7 698 15 233 675 1366 427 470 704 1108 0\n1368 53 -73 -26 -37 -15 -25 -179 -62 -79 -85 -100 55 0 1306 1299 1285 1287 1302 1300 97 39 233 1347 1320 454 151 525 202 671 427 223 1094 0\n1369 -25 -179 -62 -79 78 81 -85 188 -100 55 95 0 1298 1297 753 1299 1306 1286 1292 1301 1347 1320 101 100 99 98 97 133 454 169 728 751 746 740 525 6 7 39 53 704 418 737 735 741 747 750 726 721 715 716 679 29 698 15 233 675 1368 433 307 875 0\n1370 199 46 25 54 36 27 188 0 753 728 751 746 741 738 747 692 750 1341 726 715 721 0\n1371 46 -146 25 -167 50 87 59 54 45 43 42 69 36 78 27 81 88 188 -101 0 1246 1298 1297 662 1306 1293 1278 725 720 418 544 599 602 610 648 658 593 561 557 1370 736 737 704 3 18 28 250 698 679 531 15 714 555 675 530 284 0\n1372 -16 -73 -26 -23 -46 -11 -179 -62 -79 -85 -100 55 0 1306 1299 1289 1284 1275 1283 97 58 233 3 1347 454 151 525 68 311 671 1010 0\n1373 81 -85 178 -100 55 95 0 1246 1289 1295 753 1299 1306 1294 1302 1286 1292 1301 454 547 615 169 712 725 720 525 1356 1357 1359 132 133 1365 97 98 99 100 101 1367 1320 1347 1345 1369 374 540 597 1371 56 58 679 716 714 721 726 750 747 741 736 737 704 3 18 698 15 233 675 1372 423 433 307 1020 0\n1374 27 -112 37 36 35 25 24 -167 -81 74 66 188 0 1263 753 662 1299 1306 1298 142 141 139 138 137 728 751 746 382 692 541 738 739 598 736 747 613 750 648 726 658 721 593 715 716 561 679 557 89 290 531 555 530 233 278 698 675 36 0\n1375 54 -20 -53 -27 -23 24 -81 -85 188 -100 55 0 1246 1283 1264 1300 1298 753 16 12 152 153 228 28 18 142 141 139 137 454 154 151 725 720 525 240 675 714 715 679 721 89 290 726 750 745 747 732 741 683 736 1033 698 0\n1376 -59 -54 -20 -53 -27 -23 24 -81 -18 -85 -202 -100 0 1283 1264 1298 137 138 278 75 12 152 153 228 18 139 154 525 89 290 698 1041 736 683 741 732 744 0\n1377 -53 -27 143 -23 24 -81 -85 188 -100 55 95 0 1283 1264 1286 1298 1292 1301 753 511 1287 1293 1290 152 153 228 28 18 142 140 138 137 454 154 728 751 525 433 1375 278 530 554 556 560 590 578 1376 679 307 716 535 721 575 726 568 750 539 745 327 732 1027 683 0\n1378 -23 24 -179 -81 -85 188 -100 55 95 0 1246 1264 1283 662 1285 1287 1281 1300 1298 753 1305 1292 1304 1291 454 547 615 1320 1345 142 141 139 138 137 154 153 152 151 725 720 525 202 6 18 22 28 228 540 597 609 643 659 1374 16 1377 671 427 222 96 532 679 565 716 714 580 721 675 594 726 278 561 750 530 557 745 555 732 531 683 268 1003 0\n1379 185 23 50 87 -85 -202 0 169 154 746 740 736 735 741 704 744 1319 732 0\n1380 -203 23 50 87 -85 0 169 154 745 747 732 741 1319 737 704 0\n1381 -35 -181 78 0 29 87 679 0\n1382 -26 -180 73 0 15 73 675 0\n1383 -43 -180 73 0 36 75 675 0\n1384 24 -179 -81 -85 188 -100 55 95 0 753 1347 1320 142 141 728 751 1378 1379 1380 750 726 721 715 716 1381 1382 1383 698 49 89 679 0\n1385 54 36 -180 25 23 50 87 73 46 44 88 74 188 0 753 728 751 675 16 692 1370 739 737 744 704 732 1319 0\n1386 -79 147 -54 -37 -60 -16 -24 -81 -18 -85 -100 0 1290 1293 1298 1305 1263 1299 137 138 278 140 46 331 7 154 152 525 369 991 540 382 598 541 0\n1387 -179 -81 -85 188 -100 55 95 0 1289 1284 753 1293 1290 1298 662 142 141 140 139 138 137 454 547 615 169 155 154 153 728 751 525 202 1320 1347 1345 1384 3 7 46 69 312 1380 671 750 96 331 726 539 721 568 715 716 572 679 577 30 1385 278 530 554 556 560 589 658 648 613 1386 447 683 732 744 739 741 692 737 961 704 0\n1388 -37 -54 -4 -27 -87 -11 -24 -79 60 -81 -18 -85 -100 0 1298 1302 1295 65 140 525 287 258 999 0\n1389 -24 -186 69 -79 -184 -181 -180 60 -81 -18 -85 -100 0 1294 1264 1301 1293 1275 1277 132 142 1381 141 1383 139 138 137 169 153 152 525 3 7 46 65 229 704 692 16 234 675 1388 679 267 298 981 0\n1390 -85 178 -100 55 95 0 1246 753 712 725 153 154 454 1373 141 142 1387 674 719 718 726 715 716 750 1382 1383 1381 745 747 732 739 741 683 1319 736 737 1389 698 49 89 679 0\n1391 179 37 43 26 78 24 188 0 1246 753 725 719 718 726 716 750 1381 679 747 89 741 698 736 0\n1392 -23 -183 -184 84 47 -81 85 0 139 138 1 6 22 687 692 105 0\n1393 69 -183 -182 -184 -18 -186 -53 -20 -59 50 87 -180 -81 85 -100 0 1298 1294 1275 1306 1293 70 146 1392 137 139 290 141 1383 138 525 704 167 1340 122 123 687 5 14 227 232 692 675 1040 0\n1394 -59 -179 -180 -81 24 55 99 0 753 1263 516 1288 1289 1275 1285 1347 1320 141 1383 1382 139 138 483 1352 464 202 667 1390 712 728 751 746 740 87 89 96 335 698 671 736 735 428 741 738 744 732 733 1393 108 109 1319 692 122 0\n1395 -69 -203 -81 0 747 739 745 732 139 138 108 109 1319 692 122 0\n1396 71 -60 -45 -6 -84 -23 -54 -4 -19 -27 -182 -81 -100 0 1285 1288 1264 1283 122 1340 105 525 202 438 683 228 1012 0\n1397 -27 37 -180 -81 24 55 99 0 1263 516 1288 753 521 1284 1301 1293 1289 1275 1305 1299 1286 483 464 1352 202 667 712 142 141 1382 1383 1391 1394 679 716 721 726 750 1395 747 741 737 736 745 733 732 1347 1320 137 1390 525 10 16 24 105 122 383 234 675 1340 76 704 687 18 146 315 698 671 1396 367 445 1018 0\n1398 -23 27 -184 -81 0 139 138 6 22 692 0\n1399 -54 -6 -84 -45 -3 -60 -13 -25 -74 -88 27 -81 -100 0 1298 1281 1300 5 138 137 525 278 243 894 0\n1400 -84 -45 -3 -60 -13 -25 -74 -88 27 50 -180 -81 24 -100 0 1289 1275 521 1278 1276 141 1383 1382 140 525 315 1399 326 675 350 1140 0\n1401 53 -25 36 -74 -88 23 27 -185 -183 -179 37 -180 -81 24 85 -100 55 0 522 1297 1295 1282 1264 1300 511 1293 5 142 398 123 1347 141 1383 1382 140 525 671 91 261 698 1400 460 425 687 76 320 675 1135 0\n1402 36 -74 -88 27 -185 -184 -183 -179 37 -180 -81 24 85 -100 55 0 123 1398 139 138 692 5 1401 70 146 687 0\n1403 -53 -45 -36 -74 -88 -183 59 -180 -81 55 99 0 516 1288 1263 1285 1286 1292 1301 1306 1293 167 123 366 25 141 1383 138 137 483 1352 464 202 667 1390 525 70 146 428 433 307 687 14 232 675 1034 0\n1404 -22 -16 -18 -60 53 -45 -36 -74 -88 50 -180 -81 -100 0 1263 1302 1295 1306 1293 167 123 366 141 1383 138 137 525 14 221 232 675 1178 0\n1405 84 -60 53 -45 -36 -74 -88 -183 50 -180 -81 24 85 -100 55 0 1263 1282 1264 1300 1292 1301 511 1293 167 123 366 141 1383 140 525 460 425 1404 217 687 76 320 675 1152 0\n1406 54 -1 -6 -84 -60 -45 -36 -74 -88 -180 -81 -100 0 1263 521 1278 1276 167 123 366 141 1383 1382 140 525 326 675 350 1157 0\n1407 37 -180 -81 24 55 99 0 516 1288 753 1263 1289 1275 1292 1301 1298 1281 1300 141 1383 1382 142 138 137 483 1352 464 202 667 1390 712 525 1391 1320 1347 1394 679 716 721 726 750 745 747 732 733 739 741 736 737 1395 1397 1398 704 167 1340 123 1402 25 366 698 1403 671 1405 144 315 217 1406 278 243 1231 0\n1408 -54 -6 -84 -60 -25 -74 -88 -37 -81 -100 0 1297 522 1298 1281 1300 5 122 142 30 398 140 287 138 137 525 278 243 886 0\n1409 -84 -60 -25 -74 -88 50 -37 -180 -81 24 -100 0 1298 1297 522 1289 1275 521 1278 1276 142 30 398 140 287 141 1383 1382 525 315 1408 326 675 350 905 0\n1410 53 -25 -74 -88 -179 -183 -37 -180 -81 24 85 -100 55 0 1298 1297 522 1282 1264 1300 511 1293 5 123 142 30 398 1347 140 287 141 1383 525 671 1409 460 425 687 76 320 899 675 0\n1411 -88 -179 -183 -182 -184 -37 -180 -81 24 85 -100 55 0 30 139 138 1340 122 123 692 5 1410 70 146 687 0\n1412 -180 -81 24 55 99 0 1263 516 1288 753 141 139 138 483 1352 464 202 667 1390 712 728 751 746 740 1382 1383 1407 28 29 30 49 698 736 735 741 738 747 744 750 732 733 726 719 1320 1347 1411 704 108 1319 692 122 0\n1413 180 87 50 -186 55 -27 69 -81 0 1246 521 1296 1282 511 1287 753 198 476 458 408 202 667 1390 694 122 712 725 720 142 714 715 721 718 726 750 745 732 733 1340 704 28 679 96 671 70 146 1392 0\n1414 87 50 -186 55 -27 69 -81 0 1296 1287 521 511 1282 1276 522 1297 1284 1281 753 1293 1290 198 458 476 408 202 667 1390 383 122 105 24 16 11 10 712 728 751 743 415 201 142 141 140 1413 1383 1412 675 285 3 46 62 69 704 1340 398 375 732 731 745 687 750 726 719 721 671 716 96 331 1104 679 0\n1415 -87 55 -27 -81 0 1246 521 1296 1282 511 1287 753 198 476 458 408 202 667 1390 105 10 712 725 201 162 1320 719 718 726 715 750 1412 745 62 733 687 0\n1416 -50 55 -81 0 521 1296 1282 511 1287 1246 198 476 458 408 202 667 712 725 201 65 1347 1412 718 715 0\n1417 -13 -37 -60 -84 -4 -54 -24 -182 88 -19 -27 -81 0 521 1296 511 1287 1290 1293 522 1289 1297 1295 140 46 331 122 198 476 415 408 131 393 683 1113 0\n1418 55 -27 69 -81 0 522 1297 1296 1282 511 1287 521 1284 753 1276 1293 1290 1305 1299 1303 1285 1288 105 24 16 10 198 476 458 408 202 667 712 728 751 415 201 142 141 140 1390 383 1415 1416 1414 707 737 741 747 744 750 732 733 726 719 721 715 716 1383 1412 675 285 46 62 69 687 671 96 331 679 1417 367 392 438 360 1096 0\n1419 -37 -24 -11 -55 -27 -81 0 522 1297 1282 511 1287 753 521 1296 1276 1278 1298 1302 1295 408 80 140 34 350 16 285 105 78 10 147 198 476 458 202 667 712 141 675 715 721 726 750 745 733 687 65 3 1380 732 122 153 683 94 415 287 258 950 0\n1420 -24 -11 -55 -27 -81 0 522 1297 1246 521 1296 1282 511 1287 753 1278 1276 1305 1299 1277 198 476 458 408 202 667 712 141 16 80 675 715 721 726 750 745 732 122 105 78 10 147 733 687 153 683 725 720 714 24 415 142 140 3 34 46 65 1380 285 350 1419 214 679 298 1212 0\n1421 -87 37 -11 -55 -27 -81 0 522 1297 1298 1301 1246 521 1296 1282 511 1287 753 1291 1290 1277 1275 1420 12 198 476 458 408 202 667 712 141 16 80 675 715 721 726 750 747 741 736 142 725 720 714 1381 679 89 698 79 78 308 137 139 290 745 732 122 105 10 147 733 687 153 683 415 156 211 267 1232 0\n1422 37 -11 -55 -27 -81 0 522 1297 1246 521 1296 511 1287 753 1298 1282 1301 1285 1302 1420 198 476 458 408 202 667 712 141 16 80 675 715 721 726 750 745 732 122 105 78 10 147 733 687 153 683 747 741 736 142 725 720 714 1381 94 79 12 415 139 137 679 89 90 290 308 698 1421 1380 429 470 1179 0\n1423 87 -11 -55 -27 -81 0 522 1297 1298 1299 1301 1246 521 1296 1282 511 1287 753 1285 1302 1420 12 198 476 458 408 202 667 712 141 16 80 675 715 721 726 750 747 741 736 142 725 720 714 1381 1422 49 698 11 10 218 140 287 28 745 732 122 105 78 147 733 687 153 683 94 415 1380 429 470 1153 0\n1424 -27 69 -81 0 1297 521 1296 1282 511 1287 1246 753 1289 1295 1298 1301 1299 1284 1283 522 1277 198 476 458 408 202 667 712 725 720 415 142 141 140 10 11 12 16 105 122 1418 78 80 147 675 714 715 1381 721 726 750 745 747 732 733 741 687 736 153 374 683 1420 1422 49 88 287 218 698 1423 316 336 1158 0\n1425 -11 -87 -79 -37 -85 -55 27 -81 0 1297 1282 511 1287 1296 521 1298 1277 522 753 1278 1276 88 29 336 140 287 49 30 141 386 80 77 198 476 458 408 202 667 712 415 139 138 4 692 1370 739 736 747 750 726 721 715 1383 675 350 698 942 0\n1426 -9 -25 -87 -79 -37 -85 -55 27 -81 0 1297 521 662 1298 1277 522 1300 1302 1296 1281 157 78 79 223 532 565 88 29 336 535 140 287 539 141 386 541 596 609 641 661 150 415 408 537 906 570 244 576 528 583 551 592 562 0\n1427 -87 -79 -37 -85 -55 69 -81 0 1297 1296 521 1298 522 1277 1288 1304 1303 1302 1300 1292 1291 1306 1299 140 287 88 29 1424 141 386 153 150 80 79 78 415 408 157 336 1425 358 223 1426 339 236 879 0\n1428 -43 -25 87 -79 -37 -85 -55 27 -81 0 522 1297 1282 511 1287 1298 521 1296 1285 1302 1306 1299 753 94 470 408 202 429 140 287 28 141 386 150 198 476 458 667 712 415 1383 236 1134 715 1380 721 750 726 0\n1429 11 -79 -37 -85 -55 69 -81 0 522 1297 1282 511 1287 1298 521 1296 1285 1302 1288 1304 1303 1294 1264 1278 1276 753 94 1427 470 408 202 429 140 287 49 29 28 1424 141 386 153 152 80 77 198 476 458 667 712 728 751 415 358 229 1428 350 698 736 1379 741 898 747 675 750 715 726 721 0\n1430 -79 -37 -85 -55 69 -81 0 1282 511 1287 1296 521 1298 1285 1302 1300 1281 662 140 287 539 568 572 577 30 28 1424 141 386 541 169 150 94 80 198 476 458 408 202 667 712 139 1427 429 470 545 549 620 623 625 633 1429 4 540 1370 598 737 613 704 648 225 658 527 589 552 562 0\n1431 -37 -85 -55 69 -81 0 521 1296 1282 511 1287 753 154 153 77 1424 198 476 458 408 202 667 712 728 751 141 139 138 29 30 49 1430 683 732 745 744 750 739 741 726 692 736 721 7 715 698 1383 0\n1432 79 37 -85 -55 27 -81 0 522 1297 1282 511 1287 1296 521 753 1278 1276 1298 1263 141 386 169 154 153 152 80 77 198 476 458 408 202 667 712 728 751 415 142 140 139 138 137 447 683 732 745 744 750 739 741 726 1398 736 737 721 715 716 1383 675 1381 679 350 89 90 290 698 7 692 109 366 1103 704 0\n1433 25 37 -85 -55 27 -81 0 522 1297 1282 511 1287 1296 521 753 1278 1276 1298 1305 1299 1432 133 132 141 386 169 152 80 77 198 476 458 408 202 667 712 415 142 140 139 138 137 692 1370 369 739 736 737 747 750 726 721 715 716 1383 675 1381 679 350 89 90 290 698 3 214 704 1219 0\n1434 -87 -45 -3 35 59 -28 -9 -25 -79 -12 -85 -55 -81 0 521 1296 1297 522 1277 1284 1283 7 78 415 408 336 316 1126 0\n1435 35 -180 43 -199 -25 -79 37 -12 -85 -55 -81 0 522 1297 521 1296 1276 1278 754 1292 1301 1285 1302 673 666 711 691 686 734 693 742 748 752 727 722 717 681 141 80 675 408 140 350 737 736 7 6 133 169 94 77 202 415 215 698 1434 429 470 704 1121 0\n1436 -180 43 -199 -25 -79 37 -12 -85 -55 -81 0 522 1297 521 1296 1276 1278 511 1287 1306 1303 1282 408 80 140 350 691 686 734 693 742 748 6 79 78 415 141 139 137 675 1435 66 328 251 306 926 1380 0\n1437 43 -199 -25 -79 37 -12 -85 -55 -81 0 521 1296 1282 511 1287 1246 736 7 77 198 476 458 408 202 667 712 725 720 142 1436 714 1381 679 698 89 0\n1438 -199 37 -85 -55 27 -81 0 522 1297 511 1287 1246 1296 521 1305 1304 1306 1299 1292 1282 1301 1433 693 7 6 691 1432 686 734 141 386 150 79 78 198 476 458 408 202 667 712 725 720 415 142 139 742 748 1437 37 1383 271 236 215 714 679 90 308 1380 1235 0\n1439 37 -85 -55 27 -81 0 522 1297 511 1287 1296 521 753 1278 1276 1292 1298 1282 1301 141 386 80 79 78 77 198 476 458 408 202 667 712 728 751 415 142 140 139 137 1432 1433 6 7 1438 741 747 750 726 721 715 716 1383 675 1381 679 350 215 89 90 290 308 698 1189 1379 0\n1440 -85 -55 27 -81 0 521 1296 1282 511 1287 753 198 476 458 408 202 667 712 728 751 139 138 154 1439 30 1431 108 1319 692 732 739 744 0\n1441 25 -37 -55 27 -81 0 522 1297 511 1287 1298 753 1278 1276 1282 521 1296 1286 140 287 88 49 30 29 28 1440 147 94 80 78 77 198 476 458 408 202 667 712 728 751 415 141 139 138 692 1370 739 736 747 744 750 732 733 726 721 715 1383 675 350 698 14 65 305 687 115 123 384 683 1340 1385 957 446 0\n1442 -37 -55 27 -81 0 521 1296 1282 511 1287 753 1440 147 78 77 198 476 458 408 202 667 712 728 751 141 29 49 1441 5 7 104 687 733 745 744 750 741 726 736 721 698 715 1383 0\n1443 -25 37 85 84 47 26 -81 0 521 1296 1282 511 1287 753 198 476 458 408 202 667 712 728 751 142 141 5 7 104 687 733 745 744 750 741 726 736 721 715 716 1383 1381 679 698 89 0\n1444 74 66 -24 -9 -59 -28 -186 -36 23 85 -55 -81 0 1297 1298 521 1296 1282 511 1287 753 516 1263 1264 1283 522 1289 198 476 458 408 202 667 712 728 751 743 14 78 147 687 731 137 139 290 90 132 109 415 467 1340 246 683 704 395 1114 0\n1445 -87 -11 -74 -24 -9 -59 -28 -36 85 -55 -81 0 521 1296 522 1297 1298 1264 1300 124 137 139 290 132 415 408 424 471 1097 0\n1446 -74 -24 -9 -59 -28 -186 -36 23 25 85 -55 -81 0 522 1297 521 1296 1298 1304 1303 1285 511 1287 137 139 290 90 109 94 408 202 415 364 1445 429 479 704 992 0\n1447 87 -36 -59 -66 -5 -24 -28 -9 -55 -81 0 522 1297 521 1296 1282 753 1285 511 1287 198 476 458 408 202 667 712 728 751 123 115 132 683 732 744 741 737 384 112 65 3 94 415 429 479 704 962 0\n1448 -36 -59 -66 -5 -24 -28 -9 85 -55 -81 0 522 1297 1296 521 511 1282 1264 1300 198 458 384 115 415 408 132 1447 424 471 1111 0\n1449 -59 -66 -24 -28 -9 -55 27 -81 0 522 1297 1287 753 1277 1296 521 511 1282 1305 1299 1289 1295 198 458 384 123 115 112 1442 46 298 65 3 77 78 147 1440 1443 80 476 408 202 667 712 728 751 415 139 138 1448 692 1370 214 739 737 744 732 1340 683 372 704 1182 0\n1450 -66 -24 -28 -9 -55 27 -81 0 521 1296 1282 511 1287 753 77 78 147 1440 1442 1443 198 476 458 408 202 667 712 142 139 138 115 123 1449 679 716 721 726 750 745 747 732 739 683 692 132 0\n1451 -24 -28 -9 -55 27 -81 0 521 1296 1282 511 1287 753 14 77 78 147 1440 1442 1443 198 476 458 408 202 667 712 728 751 142 139 138 3 1450 687 733 745 744 750 739 741 726 692 737 721 716 679 1446 1444 0\n1452 197 24 43 -55 27 -81 0 521 1296 1282 511 1287 753 77 78 147 1440 1442 1443 198 476 458 408 202 667 712 728 751 142 139 138 745 744 750 739 741 726 692 736 721 25 698 716 89 679 0\n1453 -28 43 -55 27 -81 0 1282 511 1287 521 1296 1276 1278 753 408 80 140 350 77 78 147 1440 1442 1443 198 476 458 202 667 712 142 139 138 14 1451 1452 732 733 687 115 123 683 132 692 1370 739 736 747 750 726 721 716 1381 679 698 89 0\n1454 43 -55 27 -81 0 521 1296 1282 511 1287 1246 753 77 78 147 1440 1442 1443 80 198 476 458 408 202 667 712 725 720 142 141 139 138 1453 675 714 715 1381 679 721 89 726 750 745 747 732 733 739 741 692 736 132 698 2 687 115 123 683 0\n1455 -66 79 -182 0 115 123 683 0\n1456 74 -55 27 -81 0 522 1297 1304 1305 1246 1301 521 1296 1282 511 1287 753 1263 1299 516 1288 198 476 458 408 202 667 712 141 1454 1383 715 721 726 750 745 733 78 1440 147 732 138 139 77 1442 1443 747 739 692 132 1455 687 741 737 1398 1395 34 79 142 725 720 714 679 308 90 271 415 467 382 1340 683 486 704 1017 0\n1457 -87 -11 -74 -36 -59 -5 -43 85 -55 -81 0 522 1297 1301 521 1296 1282 511 1287 753 1264 1300 124 198 476 458 408 202 667 712 141 1383 715 721 726 750 745 733 78 147 732 132 1455 687 34 79 308 415 424 471 1013 0\n1458 -55 27 -81 0 522 1297 521 1296 1246 1305 1282 1301 753 1304 1303 1285 511 1287 198 476 458 408 202 667 712 725 720 415 142 141 139 138 77 78 79 94 147 1440 1442 1443 1454 34 1383 271 714 715 679 721 90 308 726 750 745 747 1395 732 733 739 741 1398 692 737 132 1455 687 1456 364 1457 429 479 704 1004 0\n1459 -43 -74 -36 55 -81 0 522 1297 1246 521 1296 1282 1303 1305 1304 753 511 1287 1285 1291 1290 23 109 364 123 30 22 1416 198 476 458 408 202 667 1390 712 725 720 415 142 141 139 35 75 1383 271 714 715 679 721 718 96 726 1320 671 750 479 70 146 428 301 745 747 733 741 687 737 1026 704 0\n1460 -22 45 43 35 55 -81 0 521 1296 1282 511 1287 753 198 476 458 408 202 667 712 201 2 9 1412 698 715 736 721 741 726 747 750 0\n1461 -192 60 55 -81 0 201 719 721 671 715 69 1412 0\n1462 54 -180 -59 -74 -36 55 -81 0 522 1297 1303 1304 1298 521 1296 1282 511 753 1278 1276 1287 1416 22 109 198 476 458 408 202 667 712 96 1461 726 750 747 741 737 123 745 733 1390 25 1459 89 1460 201 1412 62 687 162 704 435 137 139 290 23 364 415 141 140 350 675 299 998 0\n1463 -180 -59 -74 -36 27 -81 0 522 1297 1303 1304 521 1296 1282 511 1287 753 1298 1281 1300 198 476 458 408 202 667 712 1458 96 1461 726 750 747 741 737 745 733 25 1459 89 1460 137 139 290 23 109 364 123 22 1416 1390 415 201 138 1412 62 687 162 435 704 1462 278 243 980 0\n1464 -59 -74 -36 27 -81 0 1246 521 1296 1282 511 1287 753 1458 1459 123 25 198 476 458 408 202 667 1390 712 725 89 96 1460 1461 726 750 745 733 1463 715 718 671 70 146 687 0\n1465 54 -88 -84 -60 -10 -180 -74 -36 55 -81 0 521 1296 522 1297 1303 1304 1277 1278 1276 1287 30 201 1412 46 298 1459 23 109 364 415 408 141 140 350 675 299 949 0\n1466 -74 -36 27 -81 0 522 1297 1246 521 1296 1282 511 1287 1304 1303 753 1278 1277 1298 1281 1300 109 30 23 22 1458 1416 198 476 458 408 202 667 1390 712 725 720 415 201 142 140 138 137 123 364 1464 679 716 714 721 718 1412 726 1320 2 46 62 69 750 298 356 671 745 747 733 741 687 737 704 1465 278 243 1211 0\n1467 190 74 69 23 50 55 188 0 1246 753 725 721 718 726 1320 750 745 747 732 741 1340 737 704 0\n1468 -36 27 -81 0 521 1296 1282 511 1287 753 1458 1416 198 476 458 408 202 667 1390 712 201 142 22 30 109 132 1466 1467 715 716 1412 679 2 62 96 1461 726 750 745 747 732 733 741 1455 1340 687 737 162 704 0\n1469 23 69 87 88 74 27 -81 0 521 1296 1282 511 1287 753 1468 1458 1416 198 476 458 408 202 667 712 728 751 746 201 139 138 1467 704 715 737 1412 738 7 692 0\n1470 -23 27 -81 0 521 1296 1282 511 1287 753 1458 198 476 458 408 202 667 712 201 3 1398 1412 739 715 747 721 750 726 0\n1471 -69 74 27 -81 0 521 1296 1282 511 1287 753 1468 198 476 458 408 202 667 712 728 751 139 138 108 1319 692 732 739 744 0\n1472 74 27 -81 0 521 1296 1282 511 1287 753 1470 1468 1458 1416 198 476 458 408 202 667 712 728 751 201 139 138 1471 1467 715 1412 7 692 739 747 744 750 732 726 1340 719 1469 1320 0\n1473 -87 27 -81 0 521 1296 1282 511 1287 1246 753 1468 1458 198 476 458 408 202 667 712 725 201 139 138 160 1320 1461 718 726 715 750 1412 747 7 739 692 0\n1474 -25 88 27 -81 0 521 1296 1282 511 1287 753 1473 1470 1458 1416 198 476 458 408 202 667 712 201 7 108 1412 704 715 737 721 741 726 747 750 0\n1475 54 88 27 -81 0 1285 1288 522 1297 516 1298 521 1296 1282 511 753 1287 1278 1276 198 476 458 408 202 667 712 728 751 138 139 1468 1474 692 739 744 733 1472 123 1458 1390 201 747 750 726 721 715 1412 2 62 687 140 716 142 1461 96 679 287 141 1383 1416 1470 1473 746 738 737 704 135 415 486 440 675 299 350 956 0\n1476 88 27 -81 0 522 1297 521 1296 1282 511 1287 1285 516 1288 753 1298 1281 1300 1473 1472 135 123 1470 1468 1458 1416 198 476 458 408 202 667 1390 712 728 751 746 415 201 142 140 139 138 137 440 486 1474 692 738 739 737 747 744 704 750 733 726 721 1461 715 716 96 1412 679 2 62 287 687 1475 278 243 885 0\n1477 -54 -24 27 -81 0 1297 522 1264 1294 1290 1293 753 521 1296 1282 511 1287 1298 1281 1300 198 476 458 408 202 667 712 138 139 1468 7 692 739 747 750 726 721 716 142 1458 1461 96 679 140 46 331 62 1472 123 1390 2 728 751 744 733 687 1476 166 124 229 398 415 137 278 243 1218 0\n1478 -180 27 -81 0 521 1296 1282 511 1297 522 1294 1264 753 1293 1290 1287 1278 1276 142 1468 1476 398 166 1472 124 123 198 476 458 408 202 667 1458 1390 712 728 751 415 201 141 140 139 138 1383 1412 2 7 46 62 229 692 739 747 744 750 733 726 687 721 1461 716 96 331 679 1477 675 299 350 943 0\n1479 43 -84 -60 27 -81 0 1297 522 1246 1298 521 1296 1282 511 1287 753 1275 1289 1278 1276 138 139 1468 198 476 458 408 202 667 712 1478 715 721 726 750 747 739 692 7 1458 1416 315 140 725 720 714 142 96 679 287 49 741 736 1381 677 676 1476 398 1472 415 285 350 698 927 0\n1480 -84 -60 27 -81 0 1297 522 753 521 1296 1287 1246 1298 1289 1275 1306 1299 511 1282 140 198 476 458 408 202 667 712 725 720 1478 714 142 96 679 287 138 139 1468 715 721 726 750 747 739 692 7 5 1476 398 1472 1458 1416 415 145 315 1479 236 319 877 0\n1481 -60 27 -81 0 1297 522 1246 521 1287 753 1298 511 1282 1286 1296 138 139 1468 198 476 458 408 202 667 712 1478 715 721 726 750 747 739 692 7 5 741 736 745 733 142 725 720 714 1381 676 1476 398 1472 123 1458 1390 415 140 96 679 49 287 1480 460 434 687 63 242 1120 698 0\n1482 27 -81 0 521 1296 1282 511 1287 1246 753 198 476 458 408 202 667 712 725 139 138 1458 1390 1468 1472 123 1478 715 721 718 726 750 745 747 733 739 692 5 1481 671 70 146 687 0\n1483 -81 0 1296 1282 1287 511 522 1297 753 1301 521 1284 1281 1293 1290 137 138 139 140 141 142 198 201 408 415 458 476 202 667 712 728 751 743 1482 10 11 24 105 122 1424 107 110 161 166 396 1319 1395 731 750 726 721 715 716 1383 1385 234 76 80 1390 1461 1412 383 373 687 96 46 679 331 1110 0\n1484 -194 -181 -201 -180 -100 -84 -60 -27 0 516 754 1483 1297 1263 1305 1299 741 737 736 117 16 675 100 1383 525 186 182 175 667 122 453 690 160 96 92 91 378 105 24 12 11 724 752 708 748 663 734 32 50 288 684 679 698 130 368 3 214 704 1079 0\n1485 -190 -201 -180 -100 -84 -60 -27 0 1483 1263 516 753 1278 1276 1281 1300 1289 1295 741 737 736 117 16 675 1383 525 122 453 145 674 186 160 96 93 92 91 378 12 716 722 1484 750 727 745 711 732 664 1340 1319 280 704 3 28 222 698 679 136 397 683 1052 0\n1486 -201 -180 -100 -84 -60 -27 0 1246 753 1483 117 16 675 100 1383 186 182 175 667 712 94 92 91 122 12 741 736 1485 721 723 726 708 750 663 745 50 732 698 1319 3 1467 0\n1487 -24 -180 -100 -84 -60 -27 0 1263 516 1297 1295 1289 1483 753 1305 1299 186 182 175 667 712 728 751 1486 744 732 122 96 747 750 726 721 716 117 16 675 100 724 708 663 32 679 136 683 1340 397 288 525 453 378 24 214 1084 0\n1488 -180 -100 -84 -60 -27 0 1263 516 753 1483 1297 1289 1295 1287 1290 525 186 182 175 667 712 728 751 746 740 122 453 160 96 93 92 91 378 117 16 12 1383 675 100 1486 747 744 750 732 724 726 1340 1319 708 721 663 716 32 50 288 679 136 397 683 1487 698 302 735 1060 704 0\n1489 180 -84 -60 -27 0 1483 1246 753 1281 1300 1289 1295 662 1297 1306 1293 186 182 175 667 712 725 720 122 453 548 145 96 94 93 92 11 54 24 105 694 1317 677 714 715 240 721 533 726 750 745 732 1340 1319 1467 28 222 679 532 397 566 550 584 622 628 631 643 659 587 590 585 560 572 556 568 569 553 539 537 531 288 341 250 0\n1490 -84 -60 -27 0 1263 516 1483 1278 1276 1246 753 1281 1300 1289 1295 186 160 96 94 93 92 91 378 122 117 16 12 145 175 182 453 667 1489 1383 675 1488 100 1352 199 524 663 280 708 723 724 721 750 716 745 747 732 741 1340 1319 736 737 704 3 28 222 698 679 136 397 683 1066 0\n1491 -197 79 47 84 -27 0 122 105 10 732 733 683 687 153 0\n1492 -71 -45 -23 -21 -178 -78 -180 -99 -60 -27 0 1483 1263 516 1276 1278 1281 1300 1302 117 16 675 76 93 222 199 378 1383 280 524 1490 186 160 174 421 667 1186 0\n1493 -85 -178 95 0 176 183 667 0\n1494 -78 -180 100 -60 -27 0 1483 521 1276 753 1289 1295 117 16 675 76 1383 347 94 1352 199 663 710 728 751 743 1490 186 160 92 91 122 105 12 10 130 136 1491 745 744 750 741 724 736 737 708 1493 687 731 1340 683 397 704 1492 3 698 0\n1495 192 47 177 -60 -27 0 1246 753 710 1490 186 105 10 723 726 708 750 1493 745 687 733 0\n1496 183 23 -202 -60 74 0 743 160 92 733 731 744 1340 1319 741 704 737 0\n1497 -180 100 -60 -27 0 1263 516 1483 521 753 1278 1276 522 1297 1298 662 347 94 1352 199 663 710 728 751 1490 186 160 96 378 543 122 117 105 54 16 10 1383 675 280 76 530 554 556 560 1494 417 544 601 603 608 1495 721 716 679 28 287 539 568 572 577 589 658 648 1496 687 454 1345 547 615 0\n1498 43 100 -60 -27 0 1263 516 1295 1289 1302 1300 1246 753 1483 1278 521 1276 186 347 94 1352 199 663 54 11 24 1497 677 1342 708 710 715 721 726 750 745 732 122 96 725 720 714 92 1319 1467 28 679 136 683 174 667 1490 93 160 421 1340 397 747 741 736 1495 62 524 91 378 16 12 280 349 698 874 0\n1499 100 -60 -27 0 1263 516 1276 521 1483 1246 753 1289 1295 1300 1302 1305 1304 1490 186 160 96 94 93 92 378 122 54 24 11 347 1352 199 524 663 710 725 720 1497 677 714 715 1342 721 708 726 1495 750 745 732 1340 1319 1467 28 679 136 397 683 174 421 667 1498 271 340 958 0\n1500 54 -60 -27 0 1483 1282 511 1286 1246 1263 516 753 1289 1295 662 1297 1306 1293 1499 122 186 94 202 203 667 1390 467 548 712 725 720 1490 434 545 460 547 615 621 96 92 11 54 24 105 694 1317 117 16 675 714 715 721 726 750 745 732 1340 1319 1467 28 679 397 550 622 628 638 645 657 586 588 577 560 572 556 568 569 553 539 537 531 288 341 250 0\n1501 -60 -27 0 753 1483 122 105 12 10 91 94 186 1490 1499 202 203 667 712 1390 728 751 1500 75 76 100 687 733 1496 745 744 3 750 741 724 736 708 698 663 50 0\n1502 -42 -54 -23 47 -27 0 1483 1263 516 1298 521 1296 1282 1287 511 753 80 75 18 3 1501 378 105 12 10 50 192 196 199 698 405 458 476 736 202 667 741 712 1390 747 728 750 751 726 744 719 733 671 687 146 0\n1503 -194 -183 95 177 55 47 -27 0 710 1501 105 10 724 726 708 719 1493 671 687 146 0\n1504 -84 95 177 55 60 0 1246 146 175 182 671 667 719 708 723 0\n1505 -197 95 -54 -23 47 -27 0 1483 753 1246 1501 80 100 1502 663 1504 75 28 18 3 105 12 10 733 1503 750 747 741 736 698 89 687 1491 1493 136 708 679 723 716 721 0\n1506 95 -54 -23 47 -27 0 1298 1483 753 1287 1286 1289 1295 1282 511 1263 516 100 1502 663 710 728 751 743 40 278 80 75 163 64 28 18 3 1501 378 122 12 1505 745 744 750 741 724 726 1503 736 708 719 721 731 698 671 716 89 329 173 433 679 667 136 397 458 464 683 852 0\n1507 183 -78 -45 -53 -95 -196 -4 -54 -23 -27 0 1483 1263 516 1288 1285 1287 511 521 1284 1501 64 329 191 428 483 476 187 378 122 691 731 383 683 844 0\n1508 -192 -54 -23 47 -27 0 1263 1298 1483 753 516 1288 1285 511 1287 1289 1295 1506 483 476 191 187 100 1502 663 710 728 751 743 40 278 80 75 107 64 28 18 3 1501 378 105 12 11 10 719 721 671 716 146 428 1491 744 741 736 698 89 329 679 1507 687 374 1125 0\n1509 -54 -23 47 -27 0 1263 1483 1298 1288 516 753 1289 1275 511 1287 64 28 18 3 1501 378 122 40 12 75 80 100 1502 663 278 710 1506 187 476 483 1508 726 750 745 747 732 1491 741 683 146 453 315 736 671 698 1391 329 1137 0\n1510 -95 190 47 -27 0 1287 511 1276 521 1483 1246 753 721 1501 187 204 476 347 196 663 710 725 726 718 750 745 1491 146 147 671 0\n1511 191 79 95 47 -27 0 1246 753 729 725 750 712 745 1491 175 182 667 0\n1512 79 55 190 47 -27 0 753 1282 511 1276 521 1483 1510 721 1501 1511 718 671 146 173 1491 745 750 726 710 712 667 203 458 347 196 663 0\n1513 55 -23 47 -27 0 1263 516 1300 662 1483 1306 1303 1305 1299 1302 1288 1286 117 16 1509 675 715 156 1501 378 543 122 105 54 11 240 533 564 580 586 657 1512 391 369 470 544 540 549 601 597 623 603 625 611 653 631 633 628 618 548 615 616 442 547 546 454 446 0\n1514 -79 174 -55 87 -27 0 1263 516 1483 1306 1303 1305 1299 1302 1288 1285 1501 378 543 122 105 54 11 391 369 470 544 540 549 601 597 623 603 625 611 653 631 633 628 620 548 545 442 429 0\n1515 -23 47 -27 0 1291 1290 662 753 122 117 105 16 10 3 64 156 1509 675 715 721 730 751 743 1510 1513 147 180 303 532 565 580 586 657 1514 1491 745 750 726 712 1493 667 687 174 731 683 0\n1516 -89 79 47 -27 0 1313 1276 521 1483 753 122 105 10 174 175 176 193 202 683 687 755 347 731 196 743 663 751 710 728 0\n1517 188 183 197 23 -27 0 753 745 750 122 117 16 728 726 751 719 721 743 744 715 731 741 675 1340 1319 737 80 1320 1347 704 0\n1518 98 -178 89 0 1282 1287 511 458 476 667 0\n1519 -188 89 0 1483 710 712 1518 196 197 663 0\n1520 183 188 23 -27 0 733 1517 0\n1521 -84 79 47 -27 0 1263 753 1300 1281 1306 1303 1305 1304 1483 1287 511 1288 516 1516 1519 1515 1501 378 122 117 40 24 16 12 11 10 146 147 162 453 671 1512 719 715 726 1383 675 750 100 745 747 732 741 1340 1319 683 736 737 704 65 66 225 698 49 50 254 273 1391 663 1504 476 483 1149 0\n1522 79 47 -27 0 753 1515 1501 117 105 16 12 10 1516 1519 728 751 1520 1521 1491 687 745 744 169 750 741 726 736 737 719 721 715 716 1383 675 80 671 1320 1347 69 704 130 1381 698 49 89 679 0\n1523 55 -85 -183 47 -27 0 1276 521 1483 753 1246 1522 187 1493 168 133 1515 1390 347 1352 199 663 1503 708 750 723 747 719 741 1320 1347 737 704 0\n1524 87 -186 -55 47 -27 0 1300 1281 662 1522 168 133 1515 11 10 704 1514 225 657 527 588 552 562 0\n1525 -1 -87 35 53 143 23 47 36 0 1300 1281 522 1277 1302 1295 157 527 219 552 532 562 565 590 580 581 594 574 563 535 558 336 529 260 0\n1526 -59 -24 -87 -55 -85 47 -27 0 1263 516 1303 1306 1299 1305 1302 1295 1291 1483 1313 1278 34 1522 187 1493 54 11 24 80 1342 708 105 369 391 1515 378 101 260 343 663 192 196 755 353 932 0\n1527 -85 188 47 -27 0 1303 1306 1263 516 1299 1305 662 1246 753 1290 1304 1291 1483 1276 521 1277 522 725 720 1515 1520 105 11 1522 369 540 597 378 543 54 391 544 601 603 611 651 659 187 136 117 40 24 16 1493 1523 79 80 1342 675 708 715 714 721 1381 726 750 747 741 737 1524 1525 211 34 1526 336 679 32 270 663 347 354 929 0\n1528 -84 -79 -27 0 1303 1306 1483 1263 516 1299 1305 1245 1294 1302 105 11 369 540 597 378 543 54 391 544 601 603 611 654 187 168 134 1501 122 453 422 435 548 546 549 616 623 618 628 634 0\n1529 -85 47 -27 0 176 1527 1519 0\n1530 -188 -14 0 1276 1298 521 1296 1483 710 1519 193 202 347 405 663 199 0\n1531 183 -27 0 1483 1263 516 378 1530 689 1520 1515 0\n1532 -47 -27 0 1483 1263 516 1246 378 1530 725 1501 117 16 70 76 78 675 671 715 718 0\n1533 -27 0 10 105 1531 1532 1522 1529 1528 687 0\n1534 -188 0 1276 521 1313 1483 710 1519 193 202 347 755 663 196 0\n1535 191 0 1534 1246 725 0\n1536 -195 0 1534 728 0\n1537 189 0 1535 720 0\n1538 202 0 1536 753 751 0\n1539 196 0 1538 743 0\n1540 200 0 1538 746 0\n1541 198 0 1540 740 0\n1542 -89 -73 -186 -184 -183 -182 44 -181 47 23 0 1533 125 1340 1319 121 174 175 176 177 683 687 704 132 136 5 90 692 679 56 0\n1543 -79 -7 -22 85 -73 44 179 53 47 23 0 1246 753 1535 1286 1305 1299 1533 1293 1290 1534 1282 1301 1483 9 5 2 718 716 719 726 750 745 732 733 747 739 741 737 1542 125 1340 1319 121 723 132 136 187 446 369 692 1381 56 57 255 1391 679 98 90 308 663 704 708 1518 667 523 1241 0\n1544 36 -91 -98 -43 -59 -6 -21 -87 -71 -7 -22 69 -73 -184 44 23 0 1533 522 1289 1297 1302 1295 523 129 5 692 394 260 1144 0\n1545 -59 -6 -21 -87 -71 -7 -22 89 -73 44 179 23 0 1246 753 1534 516 1288 1483 1290 1293 188 9 2 719 726 750 745 732 125 1319 747 739 723 88 89 101 129 1391 38 663 708 1518 667 523 1544 388 252 1136 0\n1546 -36 59 -181 0 30 126 679 0\n1547 59 25 -184 44 -181 0 1533 1546 692 56 128 679 0\n1548 -22 85 -73 179 53 54 55 47 23 0 1534 753 1535 1296 1282 1301 718 716 715 1341 719 726 750 745 732 733 747 739 741 737 1542 125 1340 1319 2 5 239 1543 683 1547 90 308 704 1545 471 0\n1549 85 28 53 54 55 60 47 23 0 1534 753 1535 1289 1284 1302 1306 1303 1483 1276 521 1277 522 1296 671 718 716 715 1341 719 726 750 745 732 733 747 739 741 737 675 1542 125 1340 1319 121 736 1548 687 162 453 704 65 66 90 1547 53 114 371 683 136 187 470 391 679 1504 32 49 663 98 347 354 279 698 963 0\n1550 28 53 54 55 60 47 23 0 1246 1535 1534 753 1276 521 1483 671 719 726 750 745 732 718 715 723 675 125 1549 153 683 187 1493 1390 708 347 1352 663 199 0\n1551 -85 95 42 -187 55 0 1276 521 1483 1493 1390 708 347 663 0\n1552 -62 35 43 26 -185 -184 44 -181 0 99 101 698 1547 7 0\n1553 -79 71 -28 44 179 55 60 47 23 0 1246 1535 753 1281 1278 1483 1298 1533 1302 1295 1534 1264 1300 281 241 36 31 15 14 719 726 750 747 741 737 736 739 745 733 718 716 723 132 133 136 168 187 1381 1551 1552 663 276 1504 708 687 104 1547 692 88 90 260 1391 704 177 424 1518 667 523 1014 0\n1554 -59 -17 -9 -95 -84 -74 -7 -28 44 179 23 0 753 1483 1278 511 1287 516 1288 1534 1277 1533 483 476 189 162 281 36 15 719 726 750 747 741 737 739 87 88 90 129 1391 704 7 109 265 692 1021 0\n1555 177 -84 -74 71 -7 -28 44 179 55 60 23 0 1535 753 1483 1278 1298 1287 511 1288 516 1263 1306 1303 1534 162 154 281 36 15 719 726 750 747 741 737 736 739 718 716 665 1504 276 189 476 483 449 1554 1546 1547 7 108 704 66 698 49 254 1391 1028 0\n1556 71 -28 44 53 55 60 47 23 0 1535 753 1281 1300 1278 1534 1483 1276 521 1277 522 1282 1297 281 241 36 31 15 14 671 719 726 750 747 741 737 736 739 745 733 732 718 716 1553 1455 683 154 687 162 1555 713 663 670 101 347 354 1552 435 1547 29 66 1381 306 53 108 291 704 1101 0\n1557 53 54 55 60 47 23 0 1535 1534 753 671 719 718 726 715 716 750 1341 745 747 733 739 741 737 1550 14 1556 114 115 116 153 167 1547 687 90 162 704 0\n1558 185 22 -53 47 23 0 1541 1538 158 146 71 736 735 1379 741 744 732 733 687 112 123 704 1340 0\n1559 -59 -185 43 26 24 0 87 89 698 0\n1560 35 144 -185 -130 -28 -53 54 23 0 1292 1301 1303 1290 69 15 36 1559 698 307 49 341 535 537 569 575 582 591 560 562 558 552 529 527 215 212 0\n1561 -9 133 45 59 0 1292 1291 537 338 570 539 0\n1562 25 45 -161 -88 69 59 -130 -28 -53 54 55 23 0 1483 1278 1281 1295 662 1298 1276 521 511 1282 1304 1303 281 543 600 602 607 625 630 642 660 580 36 14 146 226 527 552 562 589 591 658 582 644 573 1561 276 349 347 458 460 547 615 618 634 633 628 648 548 610 441 597 364 540 0\n1563 -88 69 85 -28 54 55 60 47 23 0 1281 1278 662 1306 1303 1539 753 1300 1534 1483 1276 521 1277 522 1557 69 15 36 14 1558 1559 281 543 600 602 607 241 533 564 31 173 146 189 472 549 623 625 630 642 660 1560 29 48 1562 53 104 251 687 733 731 745 1340 750 181 452 724 726 667 721 708 716 663 679 347 354 1112 0\n1564 199 85 59 44 22 84 47 0 1540 1538 753 1534 741 738 747 744 750 733 726 687 721 104 716 1547 0\n1565 69 85 -28 54 55 60 47 23 0 1557 146 14 41 69 15 36 1558 1559 1564 737 158 71 1563 704 0\n1566 85 -28 54 55 60 47 23 0 1538 753 1534 1557 69 15 36 14 1558 1559 41 146 1565 112 687 733 745 744 750 739 726 721 716 108 1547 0\n1567 -28 54 55 60 47 23 0 1300 1281 1278 1483 1533 1296 753 1287 511 521 1276 662 1557 158 71 69 14 15 31 36 118 241 281 533 543 564 600 602 1558 1559 1566 386 454 1380 541 547 750 596 615 724 610 618 1551 646 632 476 660 647 349 1560 659 48 587 1561 582 573 0\n1568 -78 -85 -53 23 0 1538 169 154 153 158 71 130 136 704 683 737 732 741 744 0\n1569 59 44 -85 -53 55 23 0 753 1534 1538 1568 158 71 1380 750 726 721 716 724 169 154 153 679 32 1551 187 683 732 744 739 741 1547 737 108 704 0\n1570 -43 -46 -3 -69 -95 -59 -73 -85 -53 55 47 0 1287 516 1288 1283 1264 1306 1299 1533 511 1282 69 150 231 483 476 454 236 319 881 0\n1571 -95 -73 -85 -53 54 55 47 23 0 753 1534 1287 511 1288 516 1538 1264 1283 1277 1533 1291 1278 158 71 1380 750 726 721 715 1341 1569 88 716 1568 1381 454 1379 169 154 153 150 69 187 476 483 683 196 732 744 739 741 737 704 108 109 231 265 692 1570 1559 343 284 1147 0\n1572 -85 28 -53 54 55 47 23 0 753 1534 1298 173 158 71 183 1380 750 724 726 721 715 675 1571 1551 667 192 199 1390 407 0\n1573 78 174 -42 -119 -120 -73 -121 95 85 89 0 1277 1284 1281 1286 1263 1288 1303 623 628 615 618 634 649 608 295 544 599 602 605 607 610 542 645 597 638 635 540 619 629 617 624 546 550 446 373 445 365 363 0\n1574 -42 91 -73 95 85 -53 54 55 47 0 1285 1281 1284 1286 1296 662 1292 511 1282 1293 1301 433 549 623 385 548 628 428 547 615 618 634 639 659 587 579 173 50 277 537 569 572 577 586 657 1573 129 1561 573 576 582 535 564 307 533 20 317 0\n1575 22 59 74 66 44 85 87 84 50 47 23 0 1539 687 1564 731 737 1319 1340 704 0\n1576 190 74 50 55 23 0 1534 753 721 1467 726 1319 750 732 745 0\n1577 -69 42 178 -181 74 -180 -53 0 1538 753 1533 1483 158 71 130 166 706 1319 732 745 744 750 739 724 1358 708 663 0\n1578 182 42 178 -181 66 44 85 84 47 0 1539 1538 753 1483 732 731 745 744 687 750 739 5 724 1547 708 101 663 0\n1579 99 -73 -180 95 85 -53 54 55 47 23 0 1263 516 1540 1538 753 1483 71 125 1576 716 121 1341 173 158 146 523 464 1518 1574 1577 1578 1340 704 737 741 738 747 744 750 733 724 687 708 5 663 1547 101 0\n1580 71 -3 -46 -43 -59 -91 -7 -22 -182 -99 -73 -20 85 -53 0 1264 1294 1275 125 1340 1319 524 683 420 227 1195 0\n1581 5 -59 -7 -22 -182 -99 -73 95 85 -53 23 0 753 1483 1541 1304 1293 1290 1305 1299 1286 129 89 88 87 69 158 71 125 1319 1340 704 735 9 1559 173 199 200 663 737 741 747 750 724 708 667 524 433 271 252 255 1580 367 445 904 0\n1582 -182 -99 -73 44 95 85 -53 54 55 47 23 0 1286 1541 1540 1538 753 1296 1483 1278 1277 1533 522 1289 199 200 663 524 71 125 1576 716 121 433 173 158 146 69 1319 1340 704 737 735 741 738 747 744 750 733 724 687 708 5 9 239 667 1547 1559 129 1581 52 292 692 132 395 895 683 0\n1583 -5 -43 -59 -186 -7 -184 -91 -22 71 -99 -73 44 -20 -53 23 0 1483 1278 1277 1533 1263 129 5 524 121 158 71 52 292 692 109 366 704 1124 0\n1584 -88 -3 36 -46 -43 -59 -7 -91 -22 -99 -73 -20 -53 0 1284 1281 522 1297 129 5 524 121 375 398 1132 0\n1585 -180 95 28 -53 54 55 47 23 0 1286 1539 1538 1296 1305 1304 1293 1290 1264 1294 1302 433 1572 173 158 146 71 69 1341 675 121 125 1576 716 1579 199 524 1582 684 686 732 731 1578 744 687 667 739 741 5 9 239 736 737 1547 1559 87 88 89 1583 271 252 255 1584 704 420 468 923 0\n1586 -98 -177 0 1483 196 197 663 0\n1587 -62 -100 -20 -7 -186 -185 -22 -184 -18 -74 -181 -53 23 0 1292 1291 1263 1299 525 9 5 124 123 158 71 69 98 99 101 698 1547 29 1381 272 130 368 1019 704 0\n1588 -42 26 25 -185 -184 -181 24 0 38 43 1559 1547 0\n1589 -177 -7 -186 -185 -22 -184 -18 -74 -181 -53 23 0 1534 1483 1276 521 1286 69 5 9 1588 713 663 670 347 433 1587 0\n1590 59 78 26 25 -185 -184 -181 24 0 1381 1547 679 44 49 698 0\n1591 54 -181 73 -53 55 47 23 0 1246 1534 1300 753 1296 1263 1302 1295 1483 1533 173 158 146 93 71 69 1567 1572 675 715 721 1576 723 726 123 124 181 452 750 745 747 733 739 741 687 736 737 5 9 239 1589 708 1518 667 523 189 449 704 109 130 1590 1559 260 44 283 692 993 0\n1592 -3 -99 -18 -74 -88 -78 -44 -185 -22 -54 -53 0 1281 1284 1297 1302 1295 524 103 5 375 93 472 69 75 73 1559 71 17 256 698 1076 0\n1593 -99 -18 -74 -88 -78 -44 42 -185 -22 -54 -53 23 0 1281 1284 1294 1275 511 1287 1306 1303 103 5 375 93 472 58 100 524 1592 266 328 251 1069 0\n1594 -35 -100 -18 -74 -88 -78 -44 42 -22 -54 -53 0 1281 1284 511 1287 1306 1303 525 103 5 375 93 472 58 100 328 251 1055 0\n1595 -74 -88 -78 -44 42 -185 -22 -54 -53 55 23 0 1281 1284 1300 1294 1275 1292 1301 103 5 375 93 472 69 75 73 1559 146 452 1593 1352 525 1594 266 698 307 1048 0\n1596 -3 -91 -98 -12 -88 -78 -44 -185 -22 -54 -53 0 1281 1284 1297 1302 1295 523 103 5 375 93 472 69 75 73 1559 71 17 256 1146 698 0\n1597 -88 -78 -44 42 -185 -22 -54 73 -53 55 23 0 1483 1284 1281 1276 753 1294 1275 511 1287 1306 1303 136 58 100 663 103 5 173 93 167 189 472 375 1595 245 683 732 745 750 724 708 1518 667 523 1596 266 328 251 1138 0\n1598 -20 -5 -35 -71 -12 -178 88 -54 -78 -44 -22 -53 0 1287 511 1294 1302 100 328 173 1518 523 136 184 468 667 897 0\n1599 -35 -71 74 -178 88 -54 -78 -44 42 -22 -53 0 1276 511 1287 1306 1303 522 1289 1286 1263 1285 119 245 173 1518 523 100 58 150 158 328 251 1598 333 191 466 428 953 0\n1600 -95 -8 -45 -3 -71 74 -98 -54 -78 -44 -22 -53 0 1276 1286 1263 1285 119 245 523 150 191 466 428 937 0\n1601 74 88 -54 -78 -44 59 42 -185 -22 -53 23 0 1538 753 1483 1276 1294 1275 1292 1301 1286 1289 1295 173 100 663 158 71 130 704 737 741 747 750 724 708 1518 523 744 732 136 119 44 9 69 245 683 1599 266 698 307 1600 433 397 667 902 0\n1602 1 -2 25 23 24 0 1290 1303 1291 1304 206 0\n1603 2 26 28 -23 0 1533 1291 1304 207 0\n1604 2 -24 28 0 1533 1303 1304 208 0\n1605 -25 2 28 26 0 1290 1291 209 0\n1606 1 -26 23 25 0 1303 1304 210 0\n1607 3 35 37 36 -22 0 1292 1305 213 0\n1608 3 -24 36 37 0 1299 1305 214 0\n1609 3 -25 35 37 0 1301 1292 215 0\n1610 -35 22 25 1 0 1305 1299 216 0\n1611 1 -6 22 23 25 0 1281 1300 1295 1302 220 0\n1612 50 -22 6 53 0 1295 1302 221 0\n1613 6 53 -23 47 0 1300 1281 222 0\n1614 50 -25 53 47 6 0 1300 1302 223 0\n1615 1 -47 23 25 0 1295 1302 224 0\n1616 11 71 69 -22 0 1275 1294 227 0\n1617 11 71 -23 66 0 1283 1264 228 0\n1618 11 -24 66 71 69 0 1264 1294 229 0\n1619 1 -66 23 24 0 1275 1294 230 0\n1620 4 44 -22 42 43 0 1293 1306 232 0\n1621 4 -26 44 42 0 1306 1299 233 0\n1622 -42 22 26 2 0 1299 1533 1301 235 0\n1623 -43 22 2 0 1533 1299 1306 236 0\n1624 -44 22 26 2 0 1293 1301 237 0\n1625 7 -2 54 55 47 0 1281 1300 1296 238 0\n1626 -28 7 47 55 0 1281 1300 241 0\n1627 2 -47 28 0 1533 1296 242 0\n1628 2 22 -54 0 1300 1533 1281 243 0\n1629 28 -55 22 2 0 1533 1281 1296 244 0\n1630 12 74 73 -22 0 1276 245 0\n1631 22 2 26 -73 0 1264 1283 247 0\n1632 2 22 28 -74 26 0 1283 1276 248 0\n1633 5 45 46 42 -3 0 1290 1303 1306 1293 249 0\n1634 5 42 45 46 -23 0 1293 1306 250 0\n1635 -35 5 46 42 0 1303 1306 251 0\n1636 5 -36 45 42 0 1293 1290 252 0\n1637 3 35 36 23 -42 0 1290 1303 253 0\n1638 3 -45 23 36 0 1303 1306 254 0\n1639 3 -46 23 35 0 1290 1293 255 0\n1640 -3 8 59 50 60 0 1295 1302 1297 256 0\n1641 59 8 -23 60 0 1297 257 0\n1642 8 -37 50 60 0 1295 1302 258 0\n1643 3 37 36 -50 0 1297 259 0\n1644 3 -59 36 23 0 1295 1302 260 0\n1645 13 78 -23 79 0 1277 262 0\n1646 -35 13 78 69 79 0 1294 263 0\n1647 13 -37 69 79 0 1275 1294 264 0\n1648 3 35 37 -69 0 1277 265 0\n1649 3 35 23 -78 0 1275 1294 266 0\n1650 3 -79 37 35 23 0 1275 1277 267 0\n1651 5 46 45 -28 37 0 1292 1305 269 0\n1652 5 46 37 -43 0 1304 1305 271 0\n1653 5 45 -44 37 0 1291 1292 272 0\n1654 4 -45 28 44 0 1304 1305 273 0\n1655 4 -46 43 28 0 1291 1292 274 0\n1656 4 -9 28 42 44 0 1296 1298 275 0\n1657 9 62 -28 0 1298 276 0\n1658 9 -42 54 0 1296 277 0\n1659 4 44 42 -54 0 1298 278 0\n1660 4 44 -62 28 0 1296 279 0\n1661 -28 14 0 1483 1278 281 0\n1662 -42 14 73 0 1276 282 0\n1663 -43 14 73 0 1483 283 0\n1664 4 43 -73 42 0 1278 284 0\n1665 5 -10 46 42 37 0 1297 1298 286 0\n1666 -37 10 62 0 1298 287 0\n1667 10 59 -42 0 1297 288 0\n1668 46 5 42 -59 0 1298 290 0\n1669 5 -62 37 46 0 1297 291 0\n1670 15 -5 78 0 1277 1278 1483 292 0\n1671 5 -15 45 42 37 0 1277 1278 293 0\n1672 -37 15 0 1483 1278 294 0\n1673 15 78 -42 0 1277 295 0\n1674 15 -45 78 0 1483 296 0\n1675 5 45 42 -78 0 1278 297 0\n1676 7 -24 54 55 0 1287 299 0\n1677 6 -26 50 53 0 1287 300 0\n1678 7 54 26 -53 0 1290 1291 301 0\n1679 6 -54 24 53 50 0 1290 1287 302 0\n1680 6 -55 50 24 0 1290 1291 303 0\n1681 8 -6 60 35 59 0 1301 1292 1282 304 0\n1682 8 -24 60 59 0 1282 305 0\n1683 6 -35 47 53 0 1282 306 0\n1684 8 35 59 -53 0 1301 1292 307 0\n1685 24 -59 53 47 6 0 1301 1282 308 0\n1686 6 24 47 -60 0 1301 1292 309 0\n1687 16 -6 84 87 89 0 1283 1275 1284 1289 310 0\n1688 16 -24 87 84 89 0 1284 1289 312 0\n1689 16 89 87 -47 0 1275 1289 313 0\n1690 16 -50 84 89 0 1283 1284 314 0\n1691 6 -87 24 47 0 1283 1284 316 0\n1692 9 -26 62 0 1282 511 318 0\n1693 7 -43 47 55 0 1282 511 319 0\n1694 43 62 -47 9 0 1293 511 320 0\n1695 9 43 -55 62 0 1301 1293 321 0\n1696 -62 7 26 47 55 0 1301 1282 322 0\n1697 -18 54 7 47 26 0 1284 1283 1276 521 323 0\n1698 18 91 -47 0 1276 521 324 0\n1699 18 91 84 -54 0 1283 1284 325 0\n1700 10 -35 62 0 1287 511 328 0\n1701 8 -45 50 60 0 1287 511 329 0\n1702 45 -50 10 62 0 1293 511 330 0\n1703 45 10 -60 62 0 1290 1293 331 0\n1704 8 35 50 -62 60 0 1290 1287 332 0\n1705 20 95 87 -35 0 1289 522 333 0\n1706 20 -50 95 0 1277 522 334 0\n1707 20 -59 87 95 0 1275 1289 335 0\n1708 8 -87 59 35 0 1277 522 336 0\n1709 8 35 50 59 -95 0 1275 1277 337 0\n1710 10 -9 45 59 0 1291 1292 338 0\n1711 10 45 -54 59 0 1292 342 0\n1712 43 -59 54 9 0 1291 343 0\n1713 96 100 -9 98 0 1276 521 1278 344 0\n1714 96 -43 98 100 0 521 345 0\n1715 98 100 96 -54 0 1278 346 0\n1716 -62 100 0 521 1276 347 0\n1717 -96 9 54 43 0 1276 348 0\n1718 -98 54 43 9 0 1276 521 349 0\n1719 101 -10 98 96 0 1277 522 1278 351 0\n1720 101 -59 98 96 0 1278 353 0\n1721 -62 101 0 522 1277 354 0\n1722 10 45 -98 59 0 1277 522 355 0\n1723 10 45 59 62 -101 0 1277 1278 356 0\n1724 12 74 -11 73 0 1303 1304 1533 1288 357 0\n1725 12 -25 73 74 0 1288 359 0\n1726 12 -69 73 74 0 1304 1533 361 0\n1727 12 -71 73 0 1303 1304 1533 362 0\n1728 11 71 -73 25 69 0 1303 1288 363 0\n1729 11 -74 25 69 0 1303 1304 364 0\n1730 -25 78 79 13 0 1263 365 0\n1731 -71 13 36 78 0 1299 1305 367 0\n1732 11 71 25 66 -78 0 1299 1263 368 0\n1733 -79 11 66 25 0 1299 1305 369 0\n1734 17 -11 89 85 88 0 1281 1295 1284 1289 370 0\n1735 -25 17 85 88 89 0 1284 1289 371 0\n1736 17 88 -66 89 0 1295 1289 372 0\n1737 17 -69 85 89 0 1281 1284 373 0\n1738 11 25 -85 69 0 1295 1289 374 0\n1739 -88 11 25 66 0 1281 1284 375 0\n1740 25 -89 11 66 69 0 1281 1295 376 0\n1741 -12 14 44 0 1299 1306 1263 1483 516 377 0\n1742 12 74 66 -44 0 1263 516 379 0\n1743 -66 14 44 0 1306 1483 516 380 0\n1744 14 44 -74 0 1299 1306 1483 381 0\n1745 19 91 -66 0 1296 521 384 0\n1746 91 19 -73 85 0 1281 1284 385 0\n1747 12 -85 73 0 1296 1533 521 386 0\n1748 -91 12 66 73 0 1533 1281 1296 387 0\n1749 -36 15 0 1483 1288 516 388 0\n1750 13 69 -46 79 0 1288 516 389 0\n1751 15 46 -69 0 1306 1483 516 390 0\n1752 15 -79 46 0 1303 1306 1483 391 0\n1753 21 -69 95 0 1297 522 396 0\n1754 95 21 88 -78 0 1295 1289 397 0\n1755 -88 13 36 78 0 1297 522 398 0\n1756 69 -95 36 78 13 0 1295 1297 399 0\n1757 15 46 78 -14 0 1304 1305 400 0\n1758 15 46 -73 78 0 1305 403 0\n1759 -78 14 73 44 0 1304 404 0\n1760 99 96 100 -14 0 1296 521 1298 405 0\n1761 96 99 -44 100 0 521 406 0\n1762 99 96 -73 100 0 1298 407 0\n1763 14 44 -99 73 0 1296 521 410 0\n1764 14 44 73 -100 0 1296 1298 1483 411 0\n1765 101 -15 96 99 0 1297 522 1298 412 0\n1766 101 -46 96 99 0 522 413 0\n1767 101 96 -78 99 0 1298 414 0\n1768 15 46 78 -99 0 1297 522 417 0\n1769 15 46 78 -101 0 1297 1298 1483 418 0\n1770 87 -17 16 53 84 0 1300 1302 1264 1294 419 0\n1771 17 71 88 -53 85 0 1264 1294 420 0\n1772 87 -71 53 84 16 0 1302 1300 421 0\n1773 88 -84 17 71 0 1302 1294 422 0\n1774 17 -87 71 85 0 1300 1264 424 0\n1775 16 -88 53 84 0 1300 1264 425 0\n1776 -16 18 55 91 0 1287 1285 426 0\n1777 18 91 -53 0 1285 428 0\n1778 -55 89 16 87 0 1285 429 0\n1779 18 -89 55 0 1287 430 0\n1780 -91 16 53 87 0 1287 431 0\n1781 16 -20 84 53 89 0 1282 1286 432 0\n1782 20 95 -53 0 1286 433 0\n1783 16 89 -60 84 0 1286 434 0\n1784 -89 20 60 0 1282 436 0\n1785 16 -95 84 53 0 1282 437 0\n1786 19 91 -71 0 1285 439 0\n1787 17 -74 89 88 0 1285 440 0\n1788 19 -89 74 0 1288 442 0\n1789 17 -91 71 88 0 1288 443 0\n1790 17 -21 85 71 89 0 1263 1286 444 0\n1791 21 95 -71 0 1286 445 0\n1792 17 -79 89 85 0 1286 446 0\n1793 21 -89 79 0 1263 448 0\n1794 -95 17 85 71 0 1263 449 0\n1795 19 -18 74 85 0 1300 1264 450 0\n1796 19 -55 74 85 0 1264 451 0\n1797 18 -74 55 84 0 1300 452 0\n1798 97 100 98 -18 0 511 1286 1282 455 0\n1799 97 100 -55 98 0 1286 456 0\n1800 18 -100 55 84 0 1282 511 460 0\n1801 99 100 97 -19 0 516 1286 1263 461 0\n1802 99 97 100 -85 0 516 463 0\n1803 -91 99 0 516 1263 464 0\n1804 91 19 -99 74 85 0 1263 1286 466 0\n1805 21 -20 88 79 0 1302 1294 468 0\n1806 21 79 88 -60 0 1294 469 0\n1807 20 -79 87 60 0 1302 470 0\n1808 -95 98 0 511 1287 476 0\n1809 20 95 60 87 -98 0 1287 1285 478 0\n1810 20 -101 87 60 0 1287 511 479 0\n1811 101 -21 97 99 0 516 1285 1288 480 0\n1812 -95 99 0 516 1288 483 0\n1813 21 95 -99 79 88 0 1288 1285 485 0\n1814 21 -101 79 88 0 1288 516 486 0\n1815 -154 -169 0 1245 650 0\n1816 -141 -174 0 662 657 0\n1817 -142 -173 0 662 658 0\n1818 -143 -172 0 662 659 0\n1819 -144 -171 0 662 660 0\n1820 -145 -170 0 662 661 0\n1821 -177 62 42 0 1483 663 0\n1822 46 44 25 -184 36 0 1533 692 0\n1823 -177 -178 0 1534 713 0\n1824 181 180 0 1537 714 0\n1825 190 179 0 1535 718 0\n1826 187 192 0 1246 723 0\n1827 -194 192 0 1534 726 0\n1828 182 183 0 1539 731 0\n1829 185 186 0 1541 735 0\n1830 184 199 0 1540 738 0\n1831 201 197 0 1538 744 0\n1832 194 203 0 753 750 0\n1833 -194 -203 0 754 752 0\n1834 96 100 98 0 1313 755 0\n1835 101 97 99 0 1314 759 0\n1836 141 -59 22 47 55 0 1533 1315 0\n1837 -112 -12 155 78 0 1483 1348 0\n1838 199 54 36 46 25 0 1533 1534 1370 0\n1839 185 -85 23 50 87 0 1538 1379 0\n1840 78 37 24 179 26 43 0 1534 1391 0\n1841 183 -60 23 74 0 1538 1496 0\n1842 -3 -95 -98 -17 -74 -54 -78 -44 59 -185 -22 -53 0 523 130 5 1729 146 79 1797 44 9 93 71 69 17 1640 698 1223 0\n1843 59 -185 -22 -184 -181 -53 0 69 5 9 1588 1 173 158 146 79 71 70 1547 1590 58 119 130 1591 100 1597 1821 704 1601 737 181 1797 1729 1787 741 747 1832 724 708 1518 667 523 1842 1649 1700 1635 1187 0\n1844 3 -73 -43 -59 42 -22 -53 0 1 70 79 75 14 678 1585 191 1777 150 1746 1812 1808 189 187 125 1693 89 88 87 158 71 1607 1648 1749 1636 704 951 737 683 741 732 1831 0\n1845 69 -46 -3 -73 -43 -59 -22 -53 0 21 1 70 79 75 14 678 1585 191 1777 150 1746 1812 1808 189 187 125 1693 129 158 71 1756 704 939 737 683 741 732 1831 0\n1846 -185 -22 -184 -181 -53 0 150 14 9 5 1 173 79 70 69 1588 1843 1559 44 75 1693 1591 678 1585 191 1808 1812 1746 1777 1844 21 1822 1845 1737 944 0\n1847 54 -180 -182 -186 28 23 -181 -53 0 158 79 71 70 1591 1585 125 189 1319 704 0\n1848 44 -59 -74 -69 -95 -54 -184 -22 -53 0 1 109 1644 173 150 1737 1808 196 191 1777 1812 120 5 1659 1763 1822 988 0\n1849 -59 -74 -69 -95 -54 -184 45 -22 -53 0 173 150 1737 130 109 191 1777 1812 1808 1 88 1644 1848 401 1093 1653 0\n1850 -95 185 -22 -181 -53 0 1 14 1829 736 741 1831 732 747 1832 1827 721 715 1847 1830 703 701 150 5 173 158 71 189 191 1808 1812 704 1777 130 1737 1319 1849 1547 1684 1722 679 401 1118 0\n1851 -184 178 36 62 -22 -181 -53 0 5 1846 736 741 747 1832 724 708 1821 43 57 1822 0\n1852 -74 -69 95 62 -22 -181 -53 0 1782 549 1753 550 624 626 173 150 1737 546 130 109 146 79 181 1797 667 547 617 619 638 1815 608 603 1851 696 697 1744 1757 543 544 601 0\n1853 -201 -22 -181 -53 0 739 741 1846 736 0\n1854 -69 185 -22 -181 -53 0 1 14 1853 747 1832 1827 721 715 1831 732 1829 1847 100 1850 1852 1319 0\n1855 -184 -22 -181 -53 0 1853 747 1832 1827 721 715 724 1831 732 103 14 5 1 173 158 146 79 71 1846 1829 1850 1847 1782 100 1854 704 1739 1340 181 1797 667 1851 708 42 1749 1546 1586 1821 1744 524 192 1352 1765 921 0\n1856 -88 95 -22 -181 -53 0 1782 69 1855 1830 736 9 1 14 1853 747 1832 1827 721 715 1831 732 737 1847 75 1559 100 696 724 103 5 173 146 79 1739 1340 181 1797 1744 667 708 1586 1821 524 32 50 192 1667 1352 679 698 1767 1061 0\n1857 95 -22 -181 -53 0 1 14 1853 747 1832 1827 721 715 1831 732 1855 1830 737 1847 100 158 71 1856 704 1852 1319 0\n1858 -22 -181 -53 0 158 71 69 1 9 14 1853 747 1831 1832 732 1827 721 715 1855 1830 736 737 1847 75 1559 1857 189 704 130 1381 679 698 49 0\n1859 -54 -185 78 -181 24 0 1381 73 75 698 1559 49 679 0\n1860 -69 -181 -53 0 1858 146 93 79 70 69 107 112 130 1558 1859 1567 1591 1572 125 687 1319 1828 0\n1861 -197 79 22 -53 0 146 70 732 733 1455 687 153 154 683 0\n1862 26 -73 -13 -46 -59 54 -19 -71 -23 -185 -95 -53 0 118 89 18 191 1777 1812 1808 70 69 1603 698 1697 845 0\n1863 -73 -13 -46 -59 44 54 -19 -71 -23 -185 -95 -53 0 1808 196 204 1716 191 1777 1812 1862 1621 1692 896 0\n1864 54 -19 -71 -95 -181 -53 0 158 1860 71 189 1858 187 1861 1831 741 737 704 22 18 6 745 1832 1827 721 715 736 739 69 1341 1547 1822 89 1750 1863 1382 1383 698 0\n1865 74 -182 -95 -181 -53 0 1858 187 1861 734 691 158 1860 71 189 1831 741 737 704 18 6 736 739 191 1777 1812 1808 93 69 683 1804 1864 73 75 120 1628 1859 1559 698 1727 1641 1547 903 0\n1866 -74 -95 -181 -53 0 158 1860 71 189 1858 187 1861 1831 741 737 704 18 6 745 1832 1827 721 715 736 739 191 1777 1812 1808 173 93 69 125 1729 1787 1382 1383 1559 698 1641 1590 1547 1624 1341 1194 0\n1867 -11 -44 -78 -54 -183 74 -23 -95 22 -53 0 93 69 187 1861 1831 741 736 73 75 1559 1641 18 698 1628 120 191 1777 1812 1808 146 70 102 1724 687 1131 0\n1868 -54 -95 -181 -53 0 1866 1865 1828 684 158 1860 71 189 1858 187 1861 1831 741 737 704 18 6 736 739 191 1777 1812 1808 173 93 69 73 75 1628 1859 1559 698 1641 1547 1867 1732 1736 1745 848 0\n1869 -2 -95 -181 -53 0 187 1860 158 71 189 1858 1861 1831 741 737 704 22 739 6 745 1832 1827 721 715 1868 1341 1822 1750 1547 1866 1865 1828 684 736 191 1777 1812 1808 146 79 70 69 8 13 1625 1559 675 121 1728 687 1145 0\n1870 -95 -181 -53 0 1860 1858 158 146 71 70 69 187 189 191 1808 1812 1777 196 1861 745 1831 1832 739 741 1827 736 737 721 704 715 6 22 1866 1865 684 1828 1868 1341 1547 1822 1750 1869 1623 1559 1712 1621 1382 121 1728 687 1139 0\n1871 43 -18 -99 -59 54 -185 -23 -181 -53 0 1858 101 199 1821 173 1870 179 667 708 724 1832 745 1861 134 733 1826 721 715 6 22 1342 58 524 1782 1860 146 70 69 1559 1712 1621 1382 121 1728 687 1068 0\n1872 -18 -99 -59 54 -185 -23 -181 -53 0 101 199 1821 524 22 6 1870 1782 1860 1858 173 146 79 70 179 667 708 1826 724 1342 721 1832 715 745 733 1861 134 1871 1623 1693 1383 121 1728 687 1075 0\n1873 -11 -43 -7 -2 74 -91 85 -99 -59 -23 -181 -53 0 1870 1782 549 623 625 630 528 551 562 533 564 580 589 1817 652 44 524 129 163 22 6 1858 173 146 70 102 113 540 1734 687 1837 733 1828 1748 1831 683 1222 739 1822 0\n1874 66 11 -43 -7 -2 -91 85 -99 -59 -23 -181 -53 0 44 524 129 22 6 1870 1782 1858 146 70 1617 687 1791 1731 733 745 1831 1832 739 1827 1822 721 850 715 1383 0\n1875 -2 -99 -59 54 -185 -23 -181 -53 0 146 79 1872 1797 1777 454 524 163 22 6 1870 1782 1858 173 70 69 8 1625 1559 44 1873 1874 121 1743 1736 1383 715 721 1827 1832 745 747 1861 739 873 1822 0\n1876 46 -79 -66 -9 -26 -91 -99 -59 -23 -20 -53 0 121 1382 715 721 1827 1832 747 739 173 163 1736 524 199 129 89 22 6 1822 1634 1768 960 0\n1877 -66 -9 -26 43 -91 -99 -59 -23 -181 -53 0 15 524 163 1870 1782 1858 173 121 1736 1382 715 721 1827 1832 745 1861 1876 1655 402 1106 0\n1878 -71 -46 -4 -73 -9 -26 -91 -99 -59 -23 95 -53 0 524 129 22 1782 1791 1731 952 0\n1879 -99 -59 54 -185 -23 -181 -53 0 163 22 6 1870 1782 1858 146 79 70 69 199 524 1872 454 1777 1797 1875 1623 1559 1712 15 1877 687 733 745 1831 1832 739 1827 721 715 1341 675 1621 1822 1878 1828 1771 1617 683 1188 0\n1880 -194 85 178 91 95 62 54 -53 0 79 70 724 1827 708 721 1821 715 31 1574 675 0\n1881 -59 54 -185 -23 -53 0 1 173 146 79 70 101 129 681 1836 1879 1870 1816 523 1803 1352 1782 1518 1777 549 1390 547 623 1880 1832 745 733 1861 687 1792 1745 546 548 617 628 619 638 645 607 602 599 600 544 543 401 1743 0\n1882 -181 59 54 -23 -53 0 28 6 1 679 136 1861 745 1831 1832 739 1827 1547 721 1341 715 0\n1883 73 45 -180 -185 35 24 0 1383 1382 698 0\n1884 54 -185 -23 -53 0 22 18 6 1 146 79 70 69 1881 1882 716 1824 721 1341 1826 1827 1832 745 747 733 1861 739 1822 57 59 1883 187 121 1551 687 0\n1885 -23 181 -53 0 716 721 1827 1832 747 741 736 739 745 733 1826 682 681 173 158 146 93 79 70 69 1 6 18 22 1641 1884 1861 73 75 100 1628 187 1807 698 50 59 1674 1821 1551 1822 708 687 1792 1518 667 523 858 0\n1886 -45 46 181 -53 0 1824 716 79 71 1885 1576 125 70 146 721 1827 1832 745 733 158 1380 123 687 14 675 100 5 1797 181 124 747 741 737 739 1826 682 680 173 93 48 50 1701 1674 1821 708 1518 667 523 189 1794 704 109 1648 1822 1098 0\n1887 46 181 -53 0 1824 716 79 71 1885 1576 125 70 146 721 1827 1832 745 733 158 1380 123 687 14 675 100 5 1797 181 124 747 741 737 736 739 1826 682 681 680 173 69 1886 1711 1883 25 1822 43 401 1653 1821 708 1518 667 523 189 1794 704 1107 0\n1888 181 -53 0 173 158 146 79 71 70 69 681 716 1824 721 1826 1827 1832 745 747 733 741 736 737 1885 1576 1380 123 124 125 181 1797 687 1383 14 675 100 1887 57 59 402 1655 289 1821 1883 708 1518 667 523 189 1794 959 704 0\n1889 54 23 -53 0 1888 1870 93 79 70 1567 1591 1585 678 0\n1890 42 45 23 -53 0 1889 75 1888 1858 70 1558 73 69 698 1559 1711 158 71 1860 1859 136 1861 1831 741 737 704 745 1832 724 739 1568 128 127 126 1628 100 1870 1782 173 146 1665 1821 708 1518 667 523 181 1340 1828 687 104 1619 1822 880 0\n1891 45 23 -53 0 158 71 1888 1860 1858 69 70 1558 1889 1859 136 1861 1831 741 737 704 739 1568 73 75 1559 1628 120 1870 1782 146 79 1711 698 1890 43 192 196 199 1588 1662 1834 1767 104 1800 1575 1085 0\n1892 23 -53 0 1888 1870 1782 1860 1858 173 158 146 93 71 70 69 1558 1889 100 1628 1859 126 128 136 1568 1861 745 1831 1832 739 741 724 737 704 1891 50 1701 1638 1821 708 1518 667 523 181 1340 1828 687 104 1619 1154 1822 0\n1893 -66 -78 -54 -53 0 173 1888 1858 136 1861 745 1832 724 100 128 1892 6 22 1831 739 1822 43 1821 708 1518 523 1870 667 18 75 73 69 741 736 698 93 129 1641 163 1754 1628 1782 1736 851 0\n1894 -78 -54 -53 0 1888 1858 1628 100 75 73 1892 163 22 18 6 1870 1782 173 146 93 79 70 69 128 129 136 1754 1641 1861 745 1831 1832 739 741 724 1822 736 43 698 1821 1551 708 1518 667 523 181 1893 687 1742 1828 938 683 0\n1895 -44 -99 -54 -53 0 173 1888 1870 69 1894 1859 736 741 747 1832 724 100 199 1821 708 667 70 146 1831 733 1858 79 1551 687 1861 1792 524 703 1892 28 679 1628 1782 401 987 1653 0\n1896 -99 -54 -53 0 69 1888 1894 1859 736 741 747 1832 724 1858 1831 1861 733 1830 1892 28 679 1628 120 100 22 6 1870 1782 173 146 79 70 199 524 1821 1551 708 1792 687 667 1895 1822 1659 1763 1092 0\n1897 -54 -53 0 1892 22 6 1888 173 69 100 1894 1859 736 741 1830 747 1832 724 1896 523 1518 708 1821 43 57 1822 0\n1898 -53 0 70 79 146 173 1888 1858 1870 1782 1892 6 22 1897 1884 1882 700 702 736 101 1678 1712 741 1838 747 1831 57 58 1832 733 1861 1821 724 1827 708 1551 721 1518 667 1792 687 715 523 121 1743 675 1117 0\n1899 -85 79 -182 0 153 154 683 0\n1900 185 24 -178 -46 -184 25 89 44 54 0 1898 128 56 700 702 736 1829 1840 741 747 1831 1832 732 733 1827 721 715 716 1547 90 96 671 78 147 180 667 187 188 189 1455 1899 687 1 14 704 675 1319 125 0\n1901 -74 -95 -22 47 -185 24 -46 -184 25 89 44 -99 54 0 1898 1 186 1557 144 1785 189 188 14 9 55 524 125 1744 1787 675 715 1824 721 1547 1827 90 1559 1685 1644 1832 983 747 704 741 737 0\n1902 -203 74 -55 -95 -22 79 -185 24 -46 -99 0 1898 150 1796 144 1785 189 188 9 1 128 59 56 55 524 200 745 747 732 741 1319 683 737 1756 704 66 90 1702 1643 698 679 1100 1383 1824 0\n1903 -69 -6 -43 -59 -73 -19 -55 -95 -22 -46 89 -99 0 1898 1 55 1644 144 1785 150 524 1737 1214 0\n1904 -95 -22 47 79 -185 24 -46 -184 25 89 44 -99 54 0 1898 150 144 14 9 1 128 55 524 186 188 189 1785 1557 1901 1796 1902 1832 1827 721 715 716 675 1547 90 1559 1685 1644 1903 1756 704 1221 737 683 741 732 1831 0\n1905 -22 47 79 24 -178 -46 -184 25 89 44 -99 54 0 1898 1900 128 56 1 1904 667 180 181 1557 92 96 1576 679 716 0\n1906 95 22 47 66 -178 -184 25 89 44 0 1898 1493 667 180 182 687 733 745 1832 1827 719 721 671 716 96 1547 0\n1907 -43 -73 -23 55 -6 -59 -46 -95 22 47 0 1898 191 187 186 671 719 1827 1832 745 732 1899 1746 121 733 687 125 683 128 1645 1812 1808 1623 1693 1129 0\n1908 55 35 -59 -185 24 -46 -95 22 47 54 0 1898 1685 128 59 1812 1808 191 187 186 1557 671 1645 719 1825 1827 715 1832 1883 745 118 121 125 732 733 1899 683 687 1746 1907 1718 698 1655 1123 0\n1909 -19 -73 -23 -43 -55 -6 -59 -46 -95 22 47 0 125 121 128 187 1645 1623 190 188 1778 147 1812 1808 149 1192 687 683 1828 0\n1910 -73 -23 -43 -55 -6 -59 -46 25 -95 22 47 0 128 187 1645 107 1623 190 188 1778 1812 1808 125 1909 1796 1738 1238 0\n1911 -197 84 79 22 47 0 732 733 1899 1455 687 0\n1912 -181 24 -46 -184 25 44 -95 22 47 54 0 1898 190 670 1900 128 59 55 1812 1808 189 188 187 1547 1381 90 1685 1908 77 147 1778 1559 1623 1911 745 1831 1832 741 1827 737 721 715 1883 121 125 1910 1602 704 1644 1319 893 1828 687 0\n1913 190 -95 22 47 0 1898 187 186 721 1825 1827 671 1832 147 745 1911 0\n1914 -46 25 -182 85 -55 -95 22 47 0 1913 716 187 147 1911 1831 739 715 80 1341 1547 90 88 741 737 190 188 1778 1812 1808 189 55 1912 3 34 1608 704 1718 1737 1319 125 1744 675 1035 0\n1915 25 -182 85 -55 -95 22 47 0 187 147 1911 1831 741 737 739 1913 715 80 1341 716 189 188 1547 90 1914 1822 22 109 704 0\n1916 -182 85 -55 -95 22 47 0 187 147 1911 1831 741 737 736 1913 715 80 1341 190 188 1778 716 204 1716 1812 1808 189 1915 6 7 23 108 114 1735 704 683 66 90 125 1744 675 1883 1657 49 1638 679 1037 0\n1917 -66 -186 -185 -184 44 26 -181 -180 88 87 0 104 112 121 1547 1383 90 1559 704 3 0\n1918 85 -55 -95 22 47 0 188 189 1913 715 716 77 80 1341 187 147 1911 1831 739 741 736 737 1917 1916 687 1828 0\n1919 -23 25 -55 -95 22 47 0 187 147 1911 1831 739 1913 715 80 1341 716 3 22 1912 1822 0\n1920 -73 -24 -46 -69 -59 -85 -55 -95 22 0 1808 80 34 1718 87 88 1648 190 188 1778 77 196 1812 1631 1664 884 0\n1921 25 -55 -95 22 47 0 1918 154 187 147 1911 1831 741 737 739 1913 715 80 1341 190 188 1778 716 1812 1808 189 1547 87 88 90 1919 704 109 1648 1822 1912 34 1718 1920 1726 675 402 1030 0\n1922 73 -50 -25 -85 -185 -55 -181 -180 -95 0 90 66 23 7 6 80 1341 190 188 1778 204 1716 1812 1808 675 1763 1747 1883 1657 49 1638 679 1023 0\n1923 -9 -78 -3 -2 -73 -50 -25 -85 -185 44 -55 -95 0 118 66 7 190 188 1778 77 1808 196 1812 33 1656 698 859 0\n1924 -3 -2 -73 -50 -25 -85 -185 44 -55 -181 -95 0 90 53 190 188 1778 80 1808 196 204 1716 1812 26 679 1923 341 1695 1702 1633 1007 0\n1925 -55 -95 22 47 0 1913 716 715 204 1716 1812 1808 190 189 188 187 77 80 147 1778 1341 1911 1831 741 736 737 1918 1921 6 7 23 108 704 66 1922 1631 1924 1638 1643 1702 698 1672 1647 1015 0\n1926 -25 44 -95 22 47 0 1898 186 1925 671 719 1827 1832 747 741 737 736 187 745 732 1899 1911 1913 716 1808 196 1812 190 189 188 6 7 108 114 1735 1557 704 683 73 75 1628 1859 1659 66 1744 698 1649 1176 0\n1927 23 44 -95 22 47 0 1898 1913 716 186 1925 671 719 1827 1832 747 739 1926 1547 129 90 88 87 741 737 736 187 745 732 1899 1911 1808 196 1812 190 189 188 1557 704 120 1628 1859 1659 109 1648 1737 1319 1763 1822 1001 0\n1928 44 -95 22 47 0 1898 186 1925 671 719 1827 1832 747 741 736 739 1913 716 1926 1547 129 1927 3 22 1859 1822 1912 0\n1929 74 -8 -78 -45 -6 -23 -2 -54 -44 -84 -182 -95 0 187 1455 1899 1812 1808 191 683 1804 1742 1143 0\n1930 -23 -2 -44 -185 -84 -182 -181 -180 -95 47 0 1898 119 1382 1341 44 39 1812 1808 190 189 3 18 64 107 1613 1883 1859 1559 1709 1929 1787 1729 1240 0\n1931 -74 -45 -50 -78 -1 -2 -54 -44 -84 -95 0 127 42 1643 130 39 1812 1808 190 189 1787 1729 1229 0\n1932 24 23 -2 -44 -186 -185 -84 -182 -181 -180 -95 0 1341 119 42 39 187 1455 1899 1812 1808 191 189 188 1602 1859 127 130 704 66 1643 1883 1931 683 1804 1742 1155 0\n1933 -3 -74 -17 -69 -24 -2 -54 -44 -84 -181 -95 0 58 1751 130 46 1808 196 1812 26 1633 679 1009 0\n1934 -95 22 47 0 1898 186 187 188 189 190 1808 1812 1913 715 716 1925 671 719 1827 1832 745 747 732 1911 741 1899 736 737 1928 42 58 1341 1628 1930 1932 46 65 704 1737 1319 1751 1933 1644 1608 1682 1722 861 0\n1935 -69 -74 -84 -99 -24 -2 -54 -44 -181 95 0 100 46 80 43 1821 1504 1703 96 175 155 524 58 130 1753 1737 1751 679 1050 0\n1936 -37 -88 69 -74 -60 -84 -99 -24 -2 -54 -44 0 124 148 1618 135 100 46 1703 524 1672 1647 1043 0\n1937 -74 -84 -99 -24 -2 -54 23 -44 -181 95 0 43 100 1821 175 182 667 708 724 1832 747 741 737 46 80 1504 1703 96 162 148 524 65 42 124 1935 1618 704 1936 679 1608 1653 1170 0\n1938 -84 -99 -24 -2 -54 23 -44 -181 95 0 65 43 100 1821 162 175 182 667 708 724 1832 745 747 732 741 737 1937 1319 1340 704 0\n1939 89 -37 -60 -66 85 -178 -79 87 84 -99 -24 -2 -54 -44 95 0 100 46 1703 58 1752 524 1688 667 1792 864 0\n1940 87 88 69 74 -99 -24 -54 23 -44 -181 22 47 0 1898 1934 1628 1938 524 65 46 43 100 1821 80 58 704 737 741 747 1831 1832 733 1911 724 1827 136 1752 708 1551 719 687 671 96 1703 679 1939 1779 1788 847 0\n1941 -37 -17 -66 -79 -91 -87 -99 -24 -2 -54 -44 0 58 1752 160 524 65 100 1642 1666 862 0\n1942 -87 84 -99 -24 -54 -44 -181 22 47 0 524 46 43 100 1821 1628 80 58 42 1934 177 1320 719 1826 1827 708 1551 1832 667 745 733 1911 687 136 1752 1792 1941 679 1608 1653 1002 0\n1943 -79 -99 -24 -54 23 -44 -181 22 47 0 1934 1628 1938 1942 133 135 168 1940 0\n1944 37 -88 -66 -91 -16 -60 -99 -24 -2 -54 -44 -181 0 100 46 1703 96 524 42 679 1608 1653 1175 0\n1945 89 -99 -24 -54 23 -44 -181 22 47 0 1898 100 46 80 1934 1628 1938 1943 1911 745 1832 1827 719 671 1703 43 724 1551 1821 708 1942 524 1688 667 181 1841 687 112 1940 1944 1672 1029 1647 0\n1946 -99 -24 -54 23 -44 -181 22 47 0 1898 65 46 1628 100 80 58 43 1934 524 1938 1942 1943 1911 745 1831 1832 741 724 1827 737 1551 719 671 96 1703 1945 178 1779 1793 704 112 130 1751 687 679 1841 867 0\n1947 -79 -186 87 -24 0 65 3 133 168 704 0\n1948 -37 -11 -74 -88 69 -84 79 -60 -100 -24 -2 -54 -44 0 100 46 1703 525 1672 1647 1071 0\n1949 69 -84 -186 -182 -181 87 -60 -100 -24 -2 -54 -44 0 1947 1455 100 46 1703 96 525 65 3 42 39 704 1340 1739 1948 679 1608 1653 1205 0\n1950 99 -24 -54 -44 22 0 1898 46 43 100 1821 76 1934 1628 80 58 523 1352 202 525 1518 1390 708 1826 724 719 721 1832 671 1320 716 745 747 96 1703 732 741 737 1947 1911 1949 130 1753 1737 1751 1319 679 1064 0\n1951 -24 -54 -44 22 0 43 100 1821 76 1934 80 3 65 1950 1946 716 721 1576 1826 1827 135 181 708 1832 667 745 175 1911 0\n1952 -74 -99 -178 -78 -2 -45 -54 -44 -6 50 87 -60 55 -186 79 95 84 0 524 130 39 181 1797 1729 667 178 1793 704 1199 0\n1953 -89 -99 -78 -45 -44 -6 55 79 47 84 22 0 1898 1934 1911 1831 741 737 745 1832 1827 719 671 1320 1347 721 715 1341 1628 724 43 100 1821 708 1952 524 130 1551 174 178 1779 1793 1788 683 704 933 1828 687 0\n1954 182 -21 -23 -16 -91 -99 -78 -45 85 -54 -44 -6 -60 47 84 22 0 163 524 1628 684 1828 1789 687 1213 0\n1955 -23 -16 -91 74 -99 -78 -45 85 -44 -6 -60 79 47 84 22 0 524 1911 745 1832 1827 721 715 1341 1628 119 1934 163 1813 1954 1455 683 1748 1220 0\n1956 -99 -44 55 79 47 84 24 22 0 1898 1911 745 1832 724 43 1827 721 715 1341 100 1821 708 716 1831 741 736 1859 130 1628 719 671 91 119 1883 1934 1551 39 96 1546 1686 1347 1320 737 524 1952 1953 667 1783 1955 1602 1638 704 1841 1228 687 0\n1957 -44 55 79 47 84 24 22 0 1911 745 1832 1827 721 715 724 43 1341 100 1821 708 1956 523 1352 1518 202 0\n1958 55 79 47 84 24 22 0 1898 1911 745 1832 1827 721 716 715 719 1831 741 737 736 724 739 1934 671 1320 1347 91 96 1957 1547 6 104 108 704 169 178 1575 125 181 1383 1382 1883 667 1552 50 708 1821 0\n1959 -88 -5 -78 -25 -35 -62 -55 -180 47 84 22 0 1898 104 1683 66 18 1721 1716 101 80 1341 94 169 170 1775 472 1575 125 1744 1095 675 0\n1960 85 -87 88 -25 -35 -62 42 178 89 -55 -181 -180 79 47 84 0 1898 1721 1814 99 1381 1675 114 104 1683 1716 80 1341 1735 1578 683 125 1744 990 675 0\n1961 73 -85 -21 -87 -5 -78 -6 -25 -35 -62 -55 -180 0 1721 1716 80 1341 1764 675 1747 996 0\n1962 42 89 -55 79 47 84 22 0 1898 1911 745 1832 724 180 1934 667 708 1827 721 715 80 1341 77 716 1831 741 737 736 739 1821 98 99 101 1716 1721 1552 1547 18 66 1683 1381 108 1675 1959 704 1814 1960 1961 1631 1664 856 0\n1963 89 79 47 84 24 22 0 1898 1958 180 80 77 1911 745 1832 1827 721 716 715 1831 741 737 736 724 739 1934 667 708 1586 524 1962 31 32 38 50 192 194 1658 1588 1622 675 1559 698 1834 1835 1710 6 104 108 114 125 679 66 1683 683 1828 687 169 447 704 846 0\n1964 79 47 84 24 22 0 1911 745 1831 1832 739 741 1827 736 737 721 715 716 1958 77 80 94 1341 1963 174 176 177 178 193 195 202 205 1784 1793 1917 1716 1834 1835 687 1828 683 125 1744 1383 675 1559 1695 1546 1547 6 108 704 66 698 49 1638 679 918 0\n1965 -25 -50 85 -180 -55 47 84 24 22 0 80 1341 90 1564 736 1934 1706 66 1964 135 1796 180 77 136 53 104 1752 687 733 745 1832 724 1827 721 716 679 32 49 1883 698 1631 98 340 1821 708 667 193 195 202 1834 1801 1057 0\n1966 -181 25 -185 59 35 85 -180 26 47 84 24 22 0 1964 136 679 1590 49 739 1883 1831 121 733 687 0\n1967 -50 85 -180 -55 47 84 24 22 0 80 1341 77 1964 132 66 90 1564 736 1965 1966 716 721 1827 1832 745 747 733 739 687 1822 121 59 1883 0\n1968 181 25 85 -180 -55 47 84 24 22 0 1967 1680 1964 135 1796 80 1341 180 168 134 133 132 1934 681 716 1564 721 736 737 1826 1827 1832 745 747 733 739 687 1822 121 1743 57 59 675 1883 18 1610 704 177 1774 667 708 1821 1716 1721 1150 0\n1969 -185 25 85 -180 -55 47 84 24 22 0 1964 136 1968 1381 1967 1680 135 1796 80 1341 180 94 77 168 134 133 132 1934 1966 89 101 1559 1883 38 1623 121 1728 1821 687 733 745 1831 1832 739 741 724 1822 737 708 667 177 193 195 202 1784 704 1834 1801 1201 0\n1970 25 85 -180 -55 47 84 24 22 0 1967 1680 1964 135 1796 80 1341 94 168 133 132 1969 702 736 1829 741 1830 1838 1564 747 1831 57 101 1712 1832 733 1821 724 687 708 121 1743 1900 675 177 193 195 202 1784 704 1834 1801 1088 0\n1971 73 197 -180 26 78 24 0 745 1832 1827 721 716 1381 1831 741 736 1383 1883 1559 49 679 0\n1972 85 -180 -55 47 84 24 22 0 94 77 1964 168 136 135 134 133 1796 1967 548 1680 627 532 565 580 1970 6 53 104 1752 687 544 733 599 745 1831 602 1832 741 607 1827 737 721 704 716 1774 1381 546 616 618 633 643 1818 594 1971 1631 528 551 562 563 590 558 581 529 574 1650 535 1642 0\n1973 99 100 -87 -43 -25 -8 -6 -37 -2 -73 -85 -55 -79 0 88 340 1672 1762 1802 855 0\n1974 -99 -87 -43 -25 -8 -6 -37 -2 -73 -85 -55 -79 0 88 340 1672 524 865 0\n1975 -199 -25 50 -37 35 -2 -73 -85 -55 -79 24 0 94 1642 1680 1672 88 49 28 77 168 133 736 737 698 704 340 1974 1973 525 869 0\n1976 -25 50 -37 35 -2 -73 178 -85 44 -55 -79 24 0 94 1642 1680 1672 49 32 28 118 77 1975 741 747 1832 724 708 1821 98 1716 1721 1660 698 890 1839 0\n1977 25 -37 35 178 -55 36 24 0 56 49 32 80 77 1342 1838 708 736 1821 698 98 0\n1978 -100 -43 -50 -25 -85 -37 -79 -73 -55 0 88 340 176 147 1690 187 1706 77 150 1631 1672 525 868 0\n1979 99 -43 -50 -25 -85 -37 -79 -73 -55 0 1978 88 340 176 147 1690 187 1706 77 150 1631 1672 1762 1802 854 0\n1980 -43 -50 -25 -85 -37 -79 -73 -55 0 176 147 1690 187 1706 77 150 1631 1672 88 340 1979 524 866 0\n1981 -85 -37 35 -79 -73 -55 24 0 1672 544 599 602 607 88 49 32 187 132 119 147 77 150 176 1493 1631 1977 528 1976 551 1706 1690 562 549 545 623 620 625 633 643 1818 590 578 573 1561 1980 1664 1695 1716 1721 1183 0\n1982 -37 35 -79 -73 -55 24 0 187 168 134 133 132 678 125 180 147 94 80 78 77 28 49 56 88 1672 1981 1796 1972 5 1616 1838 1977 736 737 667 698 177 193 202 205 1784 340 704 1834 1765 1089 0\n1983 -50 85 35 -79 -73 -55 24 0 1982 132 678 147 78 1972 1607 134 133 1616 5 125 1796 187 136 119 180 77 90 1706 679 716 721 1826 1827 1832 747 739 741 1822 736 57 59 698 98 340 1821 708 667 193 202 1834 1762 1083 0\n1984 -89 -43 50 -3 -22 -19 37 -79 -73 -55 0 1898 1612 134 133 1616 5 1 168 136 132 94 80 177 193 202 1784 704 1834 1762 737 741 1838 747 1200 1832 679 1827 716 721 0\n1985 -99 -87 -59 -46 -17 -43 -6 -3 -22 -19 -79 -73 -55 0 134 133 1616 524 1209 0\n1986 101 -87 -59 -46 -17 -43 -6 -3 -22 -19 -79 -73 -55 0 1985 134 133 1616 1766 1835 1167 0\n1987 -43 50 -3 -22 85 37 -79 -73 -55 0 1898 125 1796 548 627 134 133 1616 540 597 609 529 558 560 1612 532 565 580 589 1817 644 637 5 187 136 132 180 80 38 98 1821 1984 667 1792 708 546 1826 1342 616 721 621 716 545 679 1778 1986 526 1174 0\n1988 -59 43 -183 25 23 -79 -73 -55 24 0 686 187 132 119 180 80 78 77 101 681 1559 736 1829 741 1830 1838 1542 747 57 667 1832 1821 708 724 0\n1989 85 35 -79 -73 -55 24 0 1898 1982 136 134 133 132 678 125 147 94 80 78 77 1796 1972 548 1 5 688 1616 1607 627 540 529 630 597 558 609 560 642 1819 591 1983 1612 532 565 582 1987 1988 679 1640 716 535 721 575 1827 569 1832 537 747 341 741 698 736 0\n1990 -201 43 25 35 36 44 26 24 0 739 741 1822 736 59 698 0\n1991 43 25 178 37 35 -79 44 -55 24 0 136 132 80 77 1990 747 1832 724 1827 708 721 716 679 101 1559 1821 736 57 1838 0\n1992 -100 -23 -59 -46 -43 -11 -6 -85 -79 -73 -55 0 94 156 1807 176 147 1687 77 150 1631 525 1171 0\n1993 99 -23 -59 -46 -43 -11 -6 -85 -79 -73 -55 0 1992 94 156 1807 176 147 1687 77 150 1631 1762 1802 1164 0\n1994 -23 -59 -46 -43 -11 -6 -85 -79 -73 -55 0 77 150 1631 176 147 94 156 1687 1807 1993 524 1206 0\n1995 -99 -87 -1 -3 -59 -46 -43 -11 -6 -85 -79 -73 -55 0 77 150 1631 524 892 0\n1996 100 -87 -1 -3 -59 -46 -43 -11 -6 -85 -79 -73 -55 0 1995 77 150 1631 1762 1802 891 0\n1997 25 50 35 -79 -73 -55 24 0 1680 77 1989 150 1631 187 1493 1982 136 133 132 119 80 1738 1991 38 98 1821 708 1826 724 1342 721 1832 716 679 1994 1650 1611 1380 1996 525 1227 0\n1998 -100 -6 -59 -3 -5 -43 -85 -25 -79 -73 -55 0 6 187 1493 38 98 1821 708 724 1832 90 1380 53 1752 77 118 1605 525 1203 0\n1999 99 -6 -59 -3 -5 -43 -85 -25 -79 -73 -55 0 1998 526 6 187 1493 38 98 1821 708 724 1832 90 1380 53 1752 77 118 1605 1765 1802 1161 0\n2000 -43 -25 -79 -73 -55 24 0 1898 187 678 147 78 5 1972 1493 53 1752 77 118 1605 6 136 37 38 51 98 1982 1671 1821 1609 708 1826 724 721 1832 716 679 90 1685 1380 1999 524 1168 0\n2001 -59 -3 -25 -79 -73 -55 24 0 1898 2000 187 678 147 78 5 1972 1493 53 1752 77 118 1605 6 80 90 101 1559 1685 1712 736 1839 741 747 1832 724 708 1586 1821 192 1834 1720 887 0\n2002 35 -25 -79 -73 -55 24 0 2000 187 678 147 78 5 1972 1493 136 77 1982 1609 2001 679 716 721 1826 1827 708 1832 747 741 736 698 50 99 1821 0\n2003 42 -35 43 -85 -25 -79 -73 -55 0 1898 6 66 136 1381 716 721 1827 1832 1380 187 1493 1826 708 78 1683 48 29 53 1752 77 118 1605 1664 1671 1821 1716 1721 889 0\n2004 -25 -79 -73 -55 24 0 1898 187 136 678 118 147 80 78 77 5 6 53 1605 1972 1752 1493 2000 2002 66 87 1683 1381 716 721 1826 1827 708 1832 1586 1380 2003 192 1658 1667 1834 1719 849 0\n2005 -85 -4 -35 25 -79 -73 -55 0 1898 132 119 136 1381 716 721 1827 1832 747 739 1822 57 1826 180 187 133 168 66 18 741 737 704 177 667 708 1821 1721 1716 78 1683 121 1733 77 150 1631 1610 1233 0\n2006 -35 43 -79 -73 -55 24 0 1898 121 2004 1733 187 168 136 133 132 678 125 119 118 180 147 78 18 66 1683 1381 716 721 1826 1827 1832 747 739 741 1822 737 57 1655 704 177 667 708 1821 1716 1721 2005 1796 1972 1734 1180 0\n2007 43 -79 -73 -55 24 0 2004 187 119 2006 1982 1989 1991 1493 0\n2008 -79 -73 -55 24 0 136 187 2004 2007 37 38 98 1982 1989 1997 1821 1493 90 708 679 1826 716 721 0\n2009 -46 -100 -87 -6 -21 -59 69 -71 -43 -22 79 -73 -55 0 525 37 125 150 1796 1 1750 1639 1046 0\n2010 -100 -87 -6 -21 -59 69 -71 -184 -43 -22 79 -73 -55 0 129 88 125 150 1796 5 119 525 2009 1758 1822 1652 1053 0\n2011 98 -5 -36 -15 100 -87 -6 -21 -59 -71 -43 -22 -73 -55 0 125 150 1796 1714 1799 969 0\n2012 46 100 -87 -6 -21 -59 -71 -184 -43 -22 -73 -55 0 129 88 125 150 1796 5 119 1758 1822 1652 2011 523 1067 0\n2013 -98 -13 -46 -71 -21 -87 -59 -6 -43 -22 -73 -55 0 1 37 1639 125 150 1796 523 1074 0\n2014 -87 -59 -6 -181 95 -43 -22 79 -73 -55 0 38 98 1821 37 125 150 1796 1 121 119 180 147 78 161 177 471 667 708 1578 724 683 1832 747 739 2010 2012 1750 1639 2013 1714 1799 976 0\n2015 69 173 -46 -164 87 -22 79 84 0 1898 631 648 1750 542 604 607 610 644 597 634 540 620 1616 545 1772 0\n2016 -46 100 -59 -6 -181 95 -43 -22 79 -73 -55 0 125 150 1796 548 2014 1707 549 623 628 532 565 580 38 37 1 121 119 180 147 78 1639 529 558 560 589 1817 2015 1753 1319 1578 667 193 1834 1762 934 0\n2017 46 -164 -20 78 37 -137 -43 25 -73 84 0 1898 631 37 121 1758 1652 544 531 599 553 602 556 607 560 643 589 1818 1817 594 648 644 561 610 634 559 597 620 529 540 545 1648 1740 1781 0\n2018 -59 -6 -181 95 -43 -22 79 -73 -55 0 532 565 580 38 37 125 150 1796 548 5 1 121 119 180 147 78 88 129 2014 1707 549 623 628 2017 1639 2016 529 202 558 667 560 1578 589 1319 1817 2015 0\n2019 59 -181 95 177 25 79 74 44 -55 0 180 80 1546 1547 697 739 1342 1831 708 732 667 683 174 0\n2020 -181 95 -43 -73 -55 24 0 1898 38 98 1821 78 147 2008 1964 5 125 119 2019 1685 2018 0\n2021 95 -43 -73 -55 24 0 38 98 1821 2008 125 180 2020 716 721 1826 1827 708 1832 667 745 174 732 683 0\n2022 181 -43 79 -73 -55 0 1898 180 78 147 34 1964 150 125 2021 1812 1804 5 1 1785 1808 189 188 702 119 680 681 682 716 340 721 1827 1832 745 747 1902 732 739 741 1652 1758 683 1319 1822 737 1105 704 0\n2023 37 -50 59 -71 -181 -22 -43 -73 -55 0 1898 5 119 1547 697 340 1546 180 150 125 34 2021 1812 1804 147 1785 1808 37 679 1607 1652 1091 0\n2024 59 -182 -43 79 -73 -55 0 1898 125 1319 683 2022 180 78 147 34 1964 150 2021 1812 1804 5 1 1785 1808 189 188 119 1547 340 1830 737 704 2023 1672 1116 1647 0\n2025 -182 -43 79 -73 -55 0 1898 180 78 147 34 1964 150 125 2021 1812 1804 5 1 1785 1808 190 189 188 702 38 119 80 683 1319 2024 90 129 1685 704 737 1830 1904 1668 1838 1758 1185 0\n2026 -43 79 -73 -55 0 119 147 80 78 34 702 2021 1964 188 189 190 1812 1 5 2022 2025 732 1831 739 741 1547 1904 737 90 1822 704 109 0\n2027 197 -95 43 79 44 -55 0 78 1934 5 2 670 1812 190 80 77 745 1831 1832 739 741 1827 1905 736 721 1822 1559 716 1546 0\n2028 -184 59 -95 79 -73 -55 0 1898 125 119 2026 2027 732 1319 683 78 1934 150 1796 1808 196 1620 5 2 1 80 1718 147 1785 670 1812 190 189 188 77 1905 1547 1822 716 25 1749 721 1827 1832 747 741 736 737 698 704 853 0\n2029 59 -95 79 -73 -55 0 1898 125 119 2026 2027 732 1319 683 78 1934 150 1796 1808 196 1620 2 1 80 1718 147 1785 1812 189 188 77 2028 695 1830 739 736 737 747 704 1832 66 1827 698 721 49 1638 986 716 679 0\n2030 -95 79 -73 -55 0 2026 125 119 78 77 188 189 1934 1 2 2027 732 1319 2029 90 1559 704 1829 0\n2031 -22 -59 79 -73 -55 0 1898 2026 80 1712 681 129 101 90 2030 125 119 180 78 77 1 2 5 150 688 1612 1559 1796 736 1829 741 1830 747 1831 1832 732 724 683 1340 1319 1542 1791 704 667 708 1586 1821 57 192 1673 1822 1834 1720 1059 0\n2032 -182 -87 -59 79 -73 -55 0 2031 147 78 177 1962 196 192 1720 1834 1911 1831 739 119 1964 7 57 1822 129 1673 471 77 1631 2026 80 1712 125 1899 683 1796 871 0\n2033 -87 -59 79 -73 -55 0 78 147 2031 1911 1831 739 1964 7 77 1631 2026 80 1712 129 121 119 161 177 471 1962 57 192 196 1673 1822 1834 1720 2032 684 1828 1618 687 1078 0\n2034 -85 87 22 50 79 44 -55 0 78 147 1911 1831 741 737 739 1964 7 3 169 176 704 1962 109 57 1822 0\n2035 -59 79 -73 -55 0 125 121 119 147 78 90 2031 1964 1911 3 1831 741 737 2033 2034 687 1828 1340 1319 704 0\n2036 197 25 59 44 0 745 1831 1832 739 1827 1547 721 716 0\n2037 199 25 59 44 0 741 1830 747 1547 1832 716 1827 721 0\n2038 -22 87 79 -73 -55 0 2035 2030 2026 125 119 180 77 1 2 5 2036 732 683 1340 174 667 2037 1319 736 737 704 66 698 50 99 1821 708 2019 1826 716 721 0\n2039 22 59 79 44 -55 0 147 78 1964 1911 7 2036 0\n2040 42 181 79 -73 -55 0 716 721 1827 1832 747 739 180 2030 119 2035 2039 2038 177 667 1826 708 682 125 5 2036 732 683 2037 736 471 78 2 1691 161 150 1796 2026 77 1620 1821 99 1716 1721 698 25 1646 1822 1032 0\n2041 181 79 -73 -55 0 119 2035 2039 5 2037 736 2 2026 77 716 721 1827 1832 747 739 2040 50 57 698 1822 25 0\n2042 -42 79 -73 -55 0 119 125 2035 2039 5 2030 2041 2019 1586 2036 732 683 2037 736 2038 471 78 2 1691 150 1796 2026 80 77 32 50 192 1658 1667 679 698 1834 1719 919 0\n2043 79 -73 -55 0 125 119 78 77 2026 2030 2035 2039 2 5 150 2038 2036 2037 1796 1691 471 732 736 683 2041 2019 1547 697 2042 1620 1821 99 1716 1721 698 1381 1635 1038 0\n2044 197 178 42 25 44 0 745 2036 1832 101 724 1821 708 0\n2045 -59 -100 -87 42 -73 -55 0 525 78 147 2043 2008 2 121 119 7 180 187 177 667 2044 733 687 34 1664 118 1604 3 133 134 1618 132 80 101 1712 1644 1821 1204 708 1342 0\n2046 -100 -87 42 -181 -73 -55 0 78 147 2043 2008 2 121 119 7 180 187 177 667 2044 733 687 133 134 1618 540 597 609 641 1820 118 1604 528 551 34 1664 530 554 556 563 595 579 46 136 94 525 2045 1682 679 535 1672 576 1190 1561 1695 0\n2047 98 -59 -46 100 -85 -87 -4 -73 -55 0 2043 2008 3 19 1639 34 1716 1695 118 1604 121 133 134 1618 1713 1799 1162 0\n2048 -87 42 -181 -73 -55 0 2043 2008 34 1664 118 1604 19 7 3 2 121 133 134 1618 187 136 132 119 180 147 80 78 177 667 2044 733 687 2046 1716 1695 1821 708 1342 56 1639 679 2047 523 1169 0\n2049 42 -181 -73 -55 0 2043 2008 699 34 19 2 187 121 119 147 78 77 2048 1947 737 741 1830 747 1831 1552 1832 733 1821 724 687 708 1493 0\n2050 -181 -73 -55 0 118 2043 2008 1604 19 7 3 2 121 133 134 1618 136 132 119 147 80 78 2049 32 57 192 196 1658 1673 1637 679 1838 1822 1713 1720 737 739 1947 1831 1198 733 687 0\n2051 -73 -55 0 147 94 78 118 119 121 2043 132 133 134 187 2008 1618 2 3 7 19 34 1604 2050 680 681 716 1650 1682 2036 2037 721 733 737 1826 1827 687 1947 1832 1493 747 708 739 1822 57 1655 1821 1716 1721 1236 0\n2052 181 -85 -87 -79 42 -24 -55 0 2051 1747 133 7 1738 180 78 2 1934 177 667 132 19 3 94 80 680 681 716 1824 1650 1682 721 1341 675 1826 1827 1741 708 1832 1821 747 1716 1721 739 1142 1822 0\n2053 -100 -28 -46 -59 -14 -85 -87 -79 -24 -55 0 3 132 1644 34 80 1712 2051 1747 133 7 1738 525 1072 0\n2054 98 -28 -46 -59 -14 -85 -87 -79 -24 -55 0 2053 3 132 1644 34 80 1712 2051 1747 133 7 1738 1834 1799 974 0\n2055 -184 44 -85 -87 -79 42 -24 -55 0 2051 1747 1741 2052 133 7 1738 180 78 2 1934 177 667 132 699 34 19 3 80 77 1547 1822 1552 1712 1644 1821 708 1826 721 715 675 2054 523 1044 0\n2056 44 -85 -87 -79 42 -24 -55 0 2052 2051 1747 133 7 1738 180 78 2 1934 177 667 136 132 65 19 94 80 1741 2055 697 739 1752 1342 747 708 1832 1821 1827 101 1716 1721 1704 721 679 715 907 675 0\n2057 -85 -87 -79 42 -24 -55 0 180 78 2 1934 177 667 136 133 132 65 19 7 2051 94 80 77 1738 1747 2052 2056 58 1624 401 1342 708 1821 101 1716 1721 1704 679 1127 0\n2058 -44 -181 -87 -79 42 -24 -55 0 134 2057 1774 135 1796 180 78 2 1934 177 667 136 132 65 19 7 147 94 80 77 58 1341 1624 401 1342 715 708 721 1821 1827 101 1716 1721 1704 1832 679 745 876 733 687 0\n2059 59 -66 44 -181 -17 -19 -87 -79 -24 -55 0 548 627 546 616 618 633 1743 543 600 602 607 643 1818 587 579 136 46 34 7 2051 94 80 1682 1547 679 535 739 1672 576 747 1561 1832 1695 1827 1716 1721 721 901 715 675 0\n2060 -100 -28 -46 -59 -14 -66 -17 -19 -87 -79 -24 -55 0 3 132 1644 34 80 1712 525 1065 0\n2061 98 -28 -46 -59 -14 -66 -17 -19 -87 -79 -24 -55 0 2060 3 132 1644 34 80 1712 1834 1799 967 0\n2062 -181 -87 -79 42 -24 -55 0 134 2057 1774 135 1796 180 78 2 1934 177 667 132 34 7 3 2051 147 80 2058 2044 733 687 1743 2059 101 1712 1644 1821 708 1826 1342 721 715 675 2061 523 1051 0\n2063 -87 -79 42 -24 -55 0 135 134 132 78 2 1934 19 7 3 2051 180 147 94 80 177 667 2057 1796 1774 2062 680 681 716 1824 1650 1682 721 1341 675 1826 1827 2044 1661 708 1832 733 1821 747 687 1716 1721 1133 739 1822 0\n2064 -79 42 -24 -55 0 78 2 1934 34 19 7 3 2051 180 147 94 80 132 135 2063 1807 1947 737 741 1838 747 1831 58 1639 402 1832 733 2037 724 1827 101 1712 721 1821 715 708 675 1493 667 1796 687 193 202 1760 1834 1056 0\n2065 42 -24 -55 0 65 34 7 3 2 2051 147 94 80 78 2064 1911 1962 745 1831 174 176 177 178 193 195 202 205 1784 1793 1832 739 741 1811 1716 1834 1827 737 1695 721 704 715 716 109 112 1341 675 1547 687 1822 1763 1644 1828 916 683 0\n2066 -24 -55 0 2051 147 80 78 2 7 2065 31 43 57 675 715 721 1827 1832 745 747 1911 739 132 1822 0\n2067 180 22 25 44 -79 -55 0 1898 187 168 136 135 133 132 2066 2051 180 147 94 78 77 676 715 1824 1629 721 1381 1826 1827 1832 745 747 733 739 741 1990 1822 1547 737 38 98 1663 90 1685 1821 708 1493 667 687 1796 177 193 195 202 1784 1801 704 1834 1080 0\n2068 -46 22 25 44 -79 -55 0 1898 136 2051 2066 147 78 2067 1972 1747 133 1738 540 1837 651 1818 587 187 1493 80 675 1661 31 1383 168 56 59 1991 18 66 87 1683 1381 1610 2037 532 716 737 565 721 704 582 1826 573 708 1561 1586 1821 1717 1834 1721 1159 0\n2069 22 25 44 -79 -55 0 187 136 132 2066 2051 147 80 78 77 2067 1383 675 1972 31 1493 2068 1838 1822 1342 736 739 708 747 1821 1832 99 1827 698 721 1381 716 0\n2070 25 44 -79 -55 0 187 168 136 133 132 2066 2051 180 80 77 2069 1 14 675 715 1824 721 1381 1826 1827 1832 747 739 741 1990 1547 737 38 98 90 704 1821 177 708 667 0\n2071 -62 -185 35 -181 -184 44 26 0 98 1552 0\n2072 180 44 -79 -55 0 2070 693 104 5 187 136 2066 147 78 77 715 1824 721 1381 1826 1827 1832 745 747 733 741 687 736 1493 708 2071 1821 38 50 698 0\n2073 187 -180 78 -55 0 2051 1383 2066 77 1826 724 721 1832 716 747 1381 741 736 1883 1559 49 679 0\n2074 -199 44 -79 -55 0 1898 2051 80 2072 675 31 187 2070 5 2066 147 78 1972 1493 136 2073 708 1821 1721 1716 99 77 1971 135 1725 1741 53 1752 693 6 736 742 1883 748 66 1683 1635 1380 947 0\n2075 -87 44 -79 -55 0 136 2051 80 2072 675 31 187 2070 5 2066 147 78 1972 1493 2073 708 1821 101 2074 741 747 1832 1827 721 716 679 1381 1721 1716 135 1725 1741 53 1752 1691 1708 941 0\n2076 44 -79 -55 0 187 168 136 135 133 2066 2051 147 94 80 78 77 2070 5 6 53 693 1725 1752 1741 2072 1383 675 1972 31 176 1493 2073 708 1821 101 1716 1721 2074 741 747 1832 1827 721 716 1381 679 1552 1829 2075 1807 1778 704 954 0\n2077 -79 -55 0 2066 80 77 132 136 2076 39 44 58 696 1341 1838 1824 736 1590 1559 0\n2078 -100 -178 91 0 202 204 667 0\n2079 -89 87 35 -44 -55 0 180 2051 80 78 2066 147 2077 1964 14 675 715 721 1826 1827 1832 747 739 5 77 1824 741 736 1588 44 698 99 1821 708 2078 341 1559 1590 1 1649 130 737 745 732 103 94 174 178 193 1784 1793 1740 683 704 1834 1761 915 0\n2080 -74 87 35 -44 -55 0 2051 80 78 2066 147 2077 1964 14 675 715 721 1827 1832 747 741 737 5 736 77 1824 739 44 1559 1590 130 1 180 1826 1588 698 99 1821 708 2079 667 189 704 1812 1778 1518 341 1649 1787 1729 985 0\n2081 87 35 -44 -55 0 2051 80 78 2066 147 2077 1964 14 675 715 721 1826 1827 1832 747 739 5 77 1824 741 736 1588 44 698 99 1821 708 341 1559 1590 1 1649 130 737 745 732 150 180 2079 667 1518 1778 189 1812 704 2080 683 1630 1796 995 0\n2082 35 -44 -55 0 44 2066 2051 80 78 147 2077 1964 14 675 715 721 1827 1832 747 739 5 77 1824 741 736 1588 1826 180 698 99 1821 708 2081 177 188 667 0\n2083 74 -87 -62 -44 -55 0 1898 2077 471 1721 1716 2066 2051 80 78 147 1964 14 675 715 721 1827 1832 747 739 5 77 1824 741 736 1588 58 2082 1635 1683 44 1559 1590 745 732 150 683 1630 1796 1024 0\n2084 -87 -62 89 -44 -55 0 1898 1721 1716 2066 2051 80 78 147 2077 1964 14 675 715 721 1827 1832 747 739 5 77 1824 741 736 1588 58 2082 1635 1683 44 1559 1590 130 170 471 2083 1787 1729 1006 0\n2085 89 95 -44 -55 0 1898 2066 2051 80 78 147 2077 1964 14 675 715 721 1827 1832 747 739 5 77 1824 741 736 1588 58 2082 1635 1683 66 44 1559 1590 130 737 745 732 1826 103 1 180 667 708 1821 1716 1721 2084 1705 704 1687 1739 1340 1011 0\n2086 -89 -44 -55 0 2082 66 78 2066 147 2077 1964 5 2051 80 14 675 715 721 1827 1832 747 741 736 77 1824 739 44 1559 1590 130 737 1 177 178 704 0\n2087 -44 -55 0 2051 80 78 2066 147 2077 1964 14 675 715 721 1827 1832 747 741 737 736 739 1824 5 1 77 44 1559 1590 130 2082 66 2086 2085 188 189 704 0\n2088 89 87 -55 0 2051 80 78 2066 147 2077 1964 14 675 715 721 1826 1827 1832 747 739 5 77 1824 741 736 1588 2087 1547 101 1821 708 90 737 1 180 667 189 1812 1904 704 1822 109 0\n2089 87 -55 0 1898 180 2051 80 78 2066 147 2077 1964 14 675 715 721 1826 1827 1832 747 739 5 77 1824 741 736 1588 2087 1547 101 1821 708 2078 1559 1663 1685 90 88 87 737 745 732 1 94 2088 174 178 193 1784 1793 683 704 1834 1760 109 1648 1822 913 0\n2090 -55 0 77 78 80 147 180 2051 2066 2077 1964 5 14 675 715 1824 721 1826 1827 1832 747 739 741 736 1588 2087 1547 101 1821 708 2089 177 188 667 0\n2091 -22 78 -87 0 2090 1898 1320 719 1827 1832 747 741 736 1825 716 160 156 2 61 1859 1557 0\n2092 -46 79 -98 -91 -43 -1 -47 -73 -59 -87 0 2090 125 1320 719 1827 1832 745 732 683 471 1803 118 1627 87 161 156 1750 1639 1156 0\n2093 79 24 25 -87 44 0 1898 2090 188 177 1320 719 1826 1827 1832 747 739 1825 716 1547 101 741 736 160 156 129 1859 1557 63 1588 1821 708 667 1803 1518 1559 1615 89 87 715 1883 118 1627 125 745 732 471 683 2092 1822 1668 1758 1148 0\n2094 24 25 -87 44 0 2090 1898 1320 719 1827 1832 747 739 1825 716 1547 129 101 89 88 87 741 736 715 1826 188 177 160 156 1883 1859 118 121 1557 63 151 1627 1615 1559 1588 1821 708 667 1518 1803 2093 132 1792 1650 1733 1822 1230 0\n2095 25 -87 44 0 1898 2090 1320 719 1827 1832 747 739 745 733 1825 716 1826 188 177 162 160 156 1547 87 88 101 129 2091 2094 34 62 1557 1911 74 120 1628 132 1650 1822 57 402 1655 1551 1821 687 1792 708 667 1518 1803 1008 0\n2096 -59 -25 -87 0 2090 1898 114 53 23 7 1320 719 1827 1832 747 741 736 745 732 1825 716 715 1826 188 177 170 160 156 87 88 89 101 129 1644 1883 1859 1758 118 125 1557 683 63 151 1627 1559 1735 38 1652 1821 708 667 1518 1803 1177 0\n2097 -79 -47 -87 44 0 2090 177 170 2095 151 1735 63 2096 53 7 5 1320 719 1827 1832 747 741 736 739 1825 716 715 1826 188 136 1752 1381 679 2071 1708 32 49 1666 1821 1883 698 708 1631 667 1518 1803 863 0\n2098 -47 -87 44 0 2090 2095 114 53 1320 719 1827 1832 747 741 736 739 745 732 1825 716 715 1826 188 177 170 162 63 76 151 1735 2097 471 683 125 181 1744 1797 675 667 31 708 1821 1716 1721 2071 1381 1635 964 0\n2099 -87 44 0 2090 1898 156 160 162 1320 719 1825 1827 716 1832 745 747 741 736 2095 5 7 2098 1557 1911 1859 136 0\n2100 -185 -181 -79 -25 47 44 0 1898 2090 136 1381 53 1752 168 135 5 1934 693 114 108 104 7 6 2099 1859 1557 92 96 1686 1841 1576 704 679 715 737 32 49 741 1883 747 118 1832 724 1551 687 175 182 453 1773 667 708 1821 1716 1721 1660 2071 989 0\n2101 185 88 -25 87 0 2090 108 6 736 1829 741 704 747 1347 1832 719 1827 0\n2102 -79 -25 47 44 0 2090 6 2099 135 168 2101 2100 716 1825 1576 1347 0\n2103 181 178 24 23 0 1898 2090 716 1824 721 1825 1826 1827 671 1347 708 1832 91 1576 747 125 741 1382 1383 736 698 50 99 1821 0\n2104 78 -26 -4 -62 -88 -100 -14 -74 -60 -6 -181 -84 79 -25 0 525 96 53 1730 679 1757 948 0\n2105 42 -88 -177 28 -74 -60 -6 -185 -181 -84 79 -25 44 0 2090 1586 524 1352 525 1744 91 693 6 1821 99 1660 2071 2104 1675 1649 1210 0\n2106 190 -60 -6 50 -185 178 -84 79 -25 44 0 2090 96 91 6 7 2103 108 23 2099 721 717 1576 1826 1827 676 677 1744 708 1832 1586 747 524 741 1352 737 525 704 2105 32 38 50 1658 1637 1667 679 698 930 0\n2107 -100 -4 -2 -54 -88 -78 -45 -14 -74 -60 -6 -84 -25 0 23 6 1638 525 888 0\n2108 28 -88 -78 -45 -74 -180 -60 -6 -84 -25 44 0 2090 23 6 1638 125 1382 1744 5 675 1632 1654 2107 1352 524 883 0\n2109 -99 -9 -7 -28 -88 -78 -45 -14 -74 -60 -6 -84 -25 0 23 6 1638 524 1042 0\n2110 -74 -60 50 -185 -25 47 44 0 1898 2090 2102 5 7 1964 1934 175 182 667 1614 2106 715 96 91 6 2103 693 108 23 2099 125 1744 1382 1883 2071 49 50 1638 679 1821 708 724 1832 747 741 737 704 2108 1626 1657 2109 1352 525 1070 0\n2111 -28 -177 35 -185 -181 -184 44 0 15 31 2071 1821 0\n2112 62 -78 -88 -177 -19 -180 -60 -6 -185 -84 -25 0 2090 91 6 1649 1586 524 1352 525 96 7 1821 38 50 1667 1883 698 1692 909 0\n2113 -78 -88 -177 -19 -180 -60 -6 -185 -181 -84 -25 44 0 2090 693 91 2111 1586 524 1352 525 53 7 6 127 1649 2112 99 1660 2071 1669 1883 979 0\n2114 -60 50 -185 -25 47 44 0 1898 2090 1614 6 7 5 1934 2102 1964 175 182 667 2103 693 114 108 53 2099 91 96 2106 715 2110 683 453 732 745 1831 1832 741 724 737 708 704 1586 524 1352 525 2111 2113 1730 1859 679 1769 675 32 1821 1660 2071 997 0\n2115 50 -185 -25 47 44 0 1898 2090 6 7 5 1934 2102 1964 175 182 667 2103 114 108 2099 1614 2114 671 1557 1504 435 719 73 75 100 120 677 1628 1859 1586 1827 1559 1821 1759 524 1832 50 192 1667 1352 745 747 1883 1767 732 741 683 737 870 704 0\n2116 -185 -25 47 44 0 1898 2090 5 7 2102 1964 1934 6 2115 66 92 1557 1504 73 75 100 698 1821 50 0\n2117 62 -180 -60 -14 -177 -74 -6 -88 45 35 26 -181 -84 -25 0 2090 1586 524 1352 525 96 125 23 6 5 1821 1723 31 32 1637 1622 675 679 1196 0\n2118 -78 -28 -7 -62 -100 -60 -14 -74 -6 -88 45 35 -84 -25 0 97 525 6 1649 1675 1217 0\n2119 -25 47 44 0 1898 2090 2099 5 6 7 53 114 1934 2102 1964 175 182 667 2103 2116 700 701 703 736 2101 741 164 747 1831 1614 1832 732 724 1827 683 708 719 721 125 1744 1586 671 715 524 96 1352 525 2117 100 1696 675 2118 1730 679 1769 940 0\n2120 185 25 44 0 2090 1898 699 700 702 736 2037 88 96 129 671 1840 0\n2121 60 24 47 44 0 1898 2090 2119 2120 671 719 1825 1826 1827 715 716 1832 745 747 733 739 1547 87 89 101 129 1883 1859 121 1557 1 22 1934 1822 57 1821 1551 1504 687 0\n2122 79 -26 -4 -62 -84 -73 -46 -23 78 -182 -6 -60 0 1721 1716 125 453 163 683 1645 1806 1025 0\n2123 -23 78 24 47 44 0 2090 2119 2121 96 2036 733 732 1686 186 91 2120 1 22 28 679 716 1824 721 1826 1827 1832 747 739 1822 57 59 1551 1883 118 121 125 687 175 453 1906 708 1821 98 1716 1721 1660 698 2122 1733 1792 1005 0\n2124 74 23 -182 -186 50 87 0 1319 1340 704 0\n2125 180 59 25 44 0 715 1824 721 1547 1827 739 1832 747 0\n2126 78 24 47 44 0 2119 2121 96 2125 2036 732 2037 737 186 92 91 2120 2099 2123 2124 125 181 1883 1382 1383 49 679 716 2103 721 667 1827 178 1832 704 747 109 1990 0\n2127 23 -178 69 -182 -186 95 50 87 0 2124 704 181 178 667 0\n2128 -178 85 66 69 -183 -182 -186 95 50 47 87 0 2127 1 687 175 182 667 0\n2129 -45 -177 0 50 99 1821 0\n2130 62 -84 -23 -71 -19 -73 -177 -78 -6 -60 24 -185 0 2090 186 163 1754 120 2129 1586 524 1352 525 96 91 1723 1821 38 1658 698 920 0\n2131 -23 24 47 44 0 2090 2126 136 2119 2121 96 2036 732 91 2120 2125 128 126 1822 739 747 1832 724 2099 92 186 2037 737 733 130 1455 1899 2128 708 2129 1883 125 683 669 1746 118 1586 524 1352 525 127 1686 1 163 687 1754 2130 98 1669 1660 698 1039 0\n2132 24 47 44 0 2119 2120 2099 2121 91 92 96 186 2037 2036 737 732 733 2125 2126 126 128 130 136 1822 1455 1899 739 747 1832 724 2128 708 2129 1883 125 2131 2124 0\n2133 -73 47 44 0 2090 1898 2132 65 3 2119 2099 120 125 1557 96 2037 2036 737 732 2124 0\n2134 -78 -62 -28 -7 -84 66 -74 -186 -60 -14 -100 -24 25 87 0 31 124 525 65 46 19 3 130 1649 1732 1675 704 1191 0\n2135 -5 69 -62 -28 -7 -60 -100 47 44 0 2099 2132 65 2119 96 2037 737 3 2036 732 2124 1729 704 2133 1764 1947 1455 2 1911 2134 525 27 52 1670 679 928 716 1822 721 739 1827 747 1832 0\n2136 46 5 -11 -88 78 -62 -28 -7 -84 -74 -60 -14 -100 -24 0 31 46 1636 1755 525 1769 1669 908 0\n2137 69 -62 -28 -7 -60 -100 47 44 0 2099 2119 2132 2133 1764 96 2037 737 65 3 2036 732 2124 1947 1455 2 1911 2134 31 525 46 19 704 1729 2135 1636 1755 2136 1639 1128 0\n2138 -46 -17 -21 -69 -62 -28 -7 -84 -74 -60 -14 -100 -24 0 525 19 3 1639 1119 0\n2139 54 -60 -177 47 44 0 2090 2119 96 2036 2132 2 2099 2037 737 1947 1911 65 3 732 2124 2125 1586 524 1352 2133 1764 543 600 602 607 1934 1823 1390 525 668 46 1676 675 533 31 564 1821 580 2137 109 1753 1737 550 546 622 616 625 618 633 643 1818 594 561 2138 1751 900 1651 1608 531 529 553 559 0\n2140 -69 46 37 59 25 44 0 109 130 1822 679 739 716 747 721 1832 1827 0\n2141 36 -11 -88 -42 -54 -84 -74 -60 -14 -100 -24 0 2 1628 528 551 562 96 46 1711 539 568 572 577 589 1817 655 540 597 612 543 525 19 3 1637 1197 1673 1755 544 542 601 606 0\n2142 -60 -177 47 44 0 2090 1586 524 1352 2133 1764 525 2132 65 46 3 2 2119 2099 96 2037 2036 737 732 1947 2124 1911 2139 100 1628 1711 1821 32 57 2140 704 1729 2141 1749 931 0\n2143 -177 47 44 0 2090 1898 2133 2132 65 3 2 2119 2099 1586 524 1352 525 1764 2142 671 1557 1810 719 1825 100 1628 1827 716 1821 1832 57 745 747 732 739 741 1547 1822 737 109 132 1749 2124 704 1729 1911 910 0\n2144 60 177 -24 47 87 0 1898 2090 2 1934 671 1504 719 1827 1832 745 747 1911 741 1947 737 0\n2145 47 44 0 2099 2119 2132 2 3 65 1934 2143 2144 96 2037 2036 737 732 1947 2124 1911 181 175 667 708 1826 724 721 1832 716 747 1547 739 0\n2146 -100 -78 -3 -28 -45 -14 -88 -74 -18 -16 -25 -60 -47 0 76 341 525 1063 0\n2147 -192 -203 -185 -182 -186 -60 44 0 2090 747 739 1833 96 91 2145 145 76 67 62 2099 721 727 715 716 709 1547 1546 668 669 6 108 1783 1698 2124 704 125 1744 1883 675 49 341 1638 679 2146 1352 524 1049 0\n2148 -25 -178 -182 -186 95 44 0 2145 67 2099 6 108 2127 0\n2149 23 -178 -201 -182 -186 -60 44 0 96 186 2148 2125 91 2145 67 63 62 2099 2124 2127 125 109 1383 1990 0\n2150 -203 -185 79 -182 -186 177 -60 44 0 1898 186 96 91 2145 145 63 62 61 2099 747 739 2147 1826 708 2148 2125 1547 682 2149 22 163 1645 1990 1822 1806 1383 1623 340 125 683 174 1772 667 1518 1803 994 0\n2151 -43 -73 -98 -91 -16 -71 -78 -23 46 -60 -47 0 61 63 1631 1803 186 163 1754 28 96 1652 340 857 0\n2152 -73 -98 -91 -16 -71 -78 -23 46 -185 177 -60 -47 0 1803 186 163 1754 665 664 91 63 62 61 1631 2151 698 1694 1664 872 0\n2153 -71 -78 -23 -180 46 -178 -185 177 -60 44 0 1898 186 163 1754 91 2145 145 76 62 2099 174 1772 667 1518 1803 2152 1883 675 1759 1727 341 1115 0\n2154 -23 -181 -180 46 -178 -185 79 -182 177 -60 44 0 2090 186 96 91 2145 145 106 76 62 28 163 679 1754 2153 683 1617 125 181 1744 1797 1883 675 667 2078 341 193 1352 1090 1834 0\n2155 -199 79 -197 -186 177 -60 44 0 732 186 96 91 2145 67 62 2099 736 2150 1832 748 724 1827 742 708 721 693 697 715 716 2154 2124 2127 125 2140 1883 49 0\n2156 199 -182 -186 177 -60 44 0 186 96 741 2037 747 2148 1832 708 724 0\n2157 89 -73 -46 -43 -178 -23 -79 -60 -47 0 96 340 61 1623 134 106 1617 186 151 145 667 1783 1792 1518 1803 984 0\n2158 -197 -186 177 -60 44 0 2090 96 91 2145 106 67 63 62 61 2099 732 2156 2155 132 134 135 136 2124 6 28 1617 2125 679 716 721 1826 1827 708 1832 747 739 1990 1822 1383 1623 340 2157 193 202 1779 1788 1762 1834 914 0\n2159 37 -43 -73 -98 -91 -181 -88 -25 -60 -47 0 1898 96 340 61 63 1631 1803 145 1775 53 91 1609 679 1652 1000 0\n2160 -43 -73 -98 -91 -181 -88 79 -25 -60 -47 0 1898 61 63 1631 1803 145 1775 108 96 340 2159 1672 1647 1022 0\n2161 -73 -98 -91 -181 -88 -185 79 -25 177 -60 -47 0 1898 1803 145 1775 23 6 665 664 96 91 63 62 61 1631 2160 698 1694 1664 49 1638 860 679 0\n2162 -186 177 -60 44 0 2090 1898 186 96 91 2145 689 145 76 67 63 62 2099 2158 745 1831 2036 734 1832 741 6 23 108 685 686 724 736 1576 704 708 715 716 178 1775 667 1518 1803 2161 1883 675 1725 1763 1971 341 1638 1016 0\n2163 73 -181 -180 -178 -182 -25 -185 88 23 -60 -47 0 2090 114 23 186 96 91 145 76 62 1883 675 49 341 1638 1661 679 136 1754 683 181 1797 667 2078 193 1352 1834 1058 0\n2164 -89 -43 -10 -37 -79 -73 -25 -60 -47 0 2090 53 1752 61 63 1631 125 193 202 1779 1788 1762 1834 917 0\n2165 177 -60 44 0 186 96 91 2145 151 145 63 62 61 665 2162 705 707 737 1829 741 2037 747 1831 53 114 1832 732 724 1827 708 721 715 716 2163 125 1631 683 136 1752 679 49 1666 698 2164 667 1783 1792 1518 1803 1036 0\n2166 -73 -25 -60 44 0 2165 1823 2145 62 6 2103 693 145 668 1783 545 669 1698 547 615 621 2129 96 91 151 76 67 63 61 2099 125 1631 1746 528 548 551 627 562 637 639 1818 590 578 573 1561 1658 1821 2071 736 1829 741 2124 1831 732 0\n2167 182 73 23 45 35 -47 0 2090 67 62 685 732 1576 1831 715 741 1883 736 0\n2168 -185 -25 -60 44 0 2165 1823 2145 62 6 2103 693 2129 91 63 698 2071 38 1821 0\n2169 -78 -62 -28 -74 -88 -14 -25 -100 -18 -16 45 -60 -47 0 31 6 525 91 1649 1675 1184 0\n2170 -25 -60 44 0 2090 2165 1586 524 1352 525 2145 1823 669 1698 145 668 1783 2129 96 91 76 67 62 2099 6 53 2103 2166 1764 2167 2168 736 1829 2101 741 2124 168 747 1832 1827 721 715 675 31 1821 2169 1730 1769 679 955 0\n2171 -60 44 0 2145 63 62 91 2165 2129 2170 2120 698 38 98 1821 0\n2172 -18 -16 25 44 0 1898 2090 2171 671 719 1826 1827 1832 747 739 2145 63 741 736 62 1825 716 1588 1547 101 1821 708 171 1518 523 2099 67 745 732 737 715 89 87 1883 125 2124 22 1822 1319 61 1559 1623 129 151 179 1795 667 187 1756 683 924 0\n2173 79 -16 25 44 0 1898 2090 2099 2171 671 719 1827 1832 747 739 1825 716 1547 2145 2172 1698 191 1707 1826 63 741 736 62 1588 101 1821 708 171 1518 523 67 745 732 737 715 89 87 1883 125 2124 22 1822 1340 61 1559 1623 129 683 1645 1805 945 0\n2174 -16 25 44 0 1898 2090 2171 671 719 1827 1832 747 739 2099 2145 67 745 732 741 737 62 736 1825 715 716 1547 89 87 1883 125 2124 22 1822 1826 63 1588 101 1821 708 61 1559 1623 151 106 171 1518 523 2172 1698 191 1707 2173 1792 1733 1215 0\n2175 25 44 0 1898 2090 2171 671 719 1827 1832 747 741 737 736 739 745 732 1825 716 715 2145 145 106 67 63 62 61 2099 1547 87 89 1559 1883 1623 125 1319 2124 22 1822 2174 1689 1772 193 195 202 1784 1779 1788 1740 683 1762 1798 935 0\n2176 44 0 1898 2090 2099 2145 67 76 145 2171 671 719 1825 1826 1827 715 716 1832 745 747 732 739 741 736 737 2175 6 53 108 704 2124 189 472 1775 125 1744 1797 2148 675 708 31 2111 1821 1381 1635 1716 1721 1109 0\n2177 -25 0 2176 39 0\n2178 -28 0 2176 41 0\n2179 -36 0 2176 42 0\n2180 -42 0 2176 43 0\n2181 -43 0 2176 44 0\n2182 -46 0 2176 58 0\n2183 -73 0 2176 119 0\n2184 184 0 2176 696 0\n2185 -47 23 0 2176 2179 2182 1898 2090 2184 2177 2181 62 63 67 76 1341 1342 1838 715 1824 736 737 1825 1576 1559 671 1320 685 1590 91 186 130 698 2127 2129 708 0\n2186 54 177 -60 69 -182 87 23 0 2179 2182 2177 186 92 1342 1838 708 737 2127 0\n2187 -100 -22 -16 -78 -88 -54 -6 -3 -45 -60 -11 -74 0 2090 2176 181 1776 525 1172 0\n2188 -16 -78 -88 -54 -3 -45 -60 -11 -74 47 0 2090 2176 46 1686 181 135 143 1776 1964 2187 1352 524 1207 0\n2189 -99 -1 -84 -78 -88 -54 -6 -3 -45 -60 -11 -74 0 2176 47 144 1624 524 1225 0\n2190 -186 -45 -185 -60 69 -74 -182 87 23 0 2179 2177 2090 2176 2129 2186 2185 46 1686 1638 47 186 92 1729 704 2127 178 2103 1859 2188 1783 144 1624 1611 2189 1352 525 1226 0\n2191 -45 -185 -60 69 -74 -182 87 23 0 2177 2179 2090 2176 186 1729 181 135 2185 46 2129 1638 1686 2186 2190 707 737 1806 741 747 1832 724 1827 708 721 667 2078 716 175 193 1779 1352 1859 1964 1834 1202 0\n2192 -54 45 -185 35 0 2181 2176 73 698 2 1951 0\n2193 -78 -84 -7 -24 -88 -62 45 -60 -11 -74 23 0 2178 2180 2176 1604 1721 1716 91 1649 1675 1237 0\n2194 -24 -88 -62 54 45 -60 -11 -74 59 23 0 2178 2090 2179 2176 1341 715 721 1827 1832 745 1721 1716 1824 135 2185 2 1604 1676 1911 2193 401 679 1755 1141 0\n2195 78 -84 -1 -26 -6 -88 -62 -181 -60 -11 -74 59 0 2179 2176 1721 1716 401 679 1755 1160 0\n2196 -185 -60 69 -74 -182 87 59 23 0 2179 2182 2181 2177 2180 2176 92 91 1729 135 2185 2191 2192 1341 1838 2186 715 1824 737 1821 721 704 1716 1721 1827 1832 745 2194 1686 698 9 1606 1911 2195 1649 1675 1234 0\n2197 -60 69 -74 -182 87 59 23 0 2179 2182 2177 2180 92 186 2196 736 1829 741 1838 2127 747 100 1832 1821 724 708 0\n2198 50 -186 -178 69 -182 87 23 0 704 2127 189 0\n2199 -95 -45 -50 -78 -99 -54 -11 -74 87 47 0 2179 1898 2090 2176 127 1643 524 154 124 1934 1794 144 1770 1797 1216 0\n2200 69 -74 -182 87 59 23 0 2177 1898 2180 2179 2181 2090 2176 181 135 2185 1729 2197 671 1557 719 1825 73 100 1826 1827 716 1821 1832 2144 708 747 2078 741 1352 736 737 524 1859 127 2198 66 164 1643 698 2199 1809 1504 667 1813 1964 1797 936 0\n2201 60 177 78 87 23 0 2090 1898 2185 671 1557 2144 719 1825 1827 716 1832 1859 747 736 741 0\n2202 185 -21 -89 -60 -99 62 -69 -74 59 47 0 2090 2179 2182 2177 2176 1779 175 524 1751 130 135 699 703 736 1686 1964 1703 741 1838 747 1087 1832 679 1827 716 721 0\n2203 -54 -185 -21 -89 -60 -99 -69 -74 23 0 2182 2090 2179 2176 1779 175 91 524 1751 135 2185 2192 46 1638 1686 1964 1081 0\n2204 95 -60 -178 -69 -74 59 23 0 2090 2176 2184 2177 181 2078 1352 1823 665 166 130 135 2185 667 1813 175 2202 2203 1341 715 1824 721 1827 1832 745 1911 2 9 1590 0\n2205 -60 -178 23 -69 -74 59 0 2204 186 0\n2206 -178 -69 -74 87 59 23 0 130 1823 2201 2205 0\n2207 187 35 78 59 0 2182 2177 2179 1826 724 1342 721 1832 716 747 679 741 49 736 2192 0\n2208 24 -62 -60 -21 -17 -69 -74 59 23 0 2182 2179 2184 2177 2176 100 1341 715 721 1827 1832 745 130 1824 679 1838 736 1721 1716 1751 135 2185 1686 1590 9 1606 1911 1151 0\n2209 -60 178 -69 -74 59 23 0 2182 2180 2178 2090 2176 670 1753 166 668 1787 1751 130 135 2185 91 2207 708 1821 100 1716 1721 1341 715 1824 721 679 1827 1832 745 2208 2 1604 1676 1911 878 0\n2210 -74 -182 87 59 23 0 2090 1898 2180 2185 2200 130 2206 2209 1557 2201 100 1821 0\n2211 22 79 177 60 47 0 1898 2090 671 719 1827 1832 745 1934 1911 1504 0\n2212 95 -22 -45 -50 -12 -71 -78 -178 -54 88 0 2179 2176 174 144 1690 1518 523 127 1643 667 1706 1754 925 0\n2213 60 74 -182 87 23 0 2090 1898 2180 2179 2181 2176 1340 2185 671 1557 719 73 100 1826 1827 1821 1832 708 2201 2144 747 127 136 741 1455 1899 683 736 737 1742 174 2124 1518 66 1643 523 698 2211 144 1690 2212 191 1804 1699 946 0\n2214 -182 87 59 23 0 2090 2182 2183 2179 2184 2177 1898 2176 2185 2210 1319 1340 2213 91 92 186 1841 704 1576 734 737 1829 715 716 741 1838 2192 1382 747 46 2129 1638 1832 1686 1590 724 136 1754 708 1455 683 1742 174 1518 667 523 182 1780 1911 1193 0\n2215 87 59 23 0 2090 2179 2184 2177 1898 2183 2176 2185 2214 684 685 686 732 745 1831 1832 741 724 1827 736 737 719 721 671 1347 715 716 91 186 1341 1382 2192 46 2129 1638 1686 1590 708 130 704 178 1518 667 523 182 1780 1964 1630 1616 1239 0\n2216 35 -78 59 23 0 2090 2180 1898 2176 2215 157 2185 160 1557 100 1821 136 2211 1612 177 188 1320 719 1826 708 667 181 1827 1832 745 732 1455 1742 683 170 1754 747 741 736 1518 523 1681 2192 1649 1130 0\n2217 -78 59 23 0 2090 1898 2180 2182 2176 2215 177 188 1320 719 1826 2185 160 1557 100 1821 708 667 181 1518 523 1827 1832 745 732 170 157 136 1754 1455 683 2211 1742 1612 2216 1635 1700 1122 0\n2218 59 23 0 2090 1898 2176 2185 2215 160 1320 1557 719 1825 1827 716 1832 747 741 736 2217 2091 1859 1951 0\n2219 23 0 2090 1898 2181 2185 2218 87 88 89 96 129 671 1557 73 2192 1840 699 0\n2220 -22 0 2219 1 0\n2221 -24 0 2219 3 0\n2222 -35 0 2219 18 0\n2223 -37 0 2219 28 0\n2224 -50 0 2219 64 0\n2225 -69 0 2219 107 0\n2226 -87 0 2219 156 0\n2227 -88 0 2219 163 0\n2228 186 0 2219 705 0\n2229 60 0 2090 1898 2176 2183 2221 2181 2223 2180 2220 671 1825 715 1341 1382 76 100 1840 1821 136 2211 0\n2230 -59 0 2229 96 0\n2231 -95 0 2229 186 0\n2232 -71 -99 -54 -78 0 2227 1898 2224 2231 2220 2221 2180 2222 2183 2229 2176 2219 524 100 1821 136 76 1964 175 182 667 708 724 1832 747 741 736 2192 1679 1628 1754 1727 1786 1073 0\n2233 -99 -54 -78 0 2227 1898 2224 2231 2220 2221 2180 2222 2229 2176 2219 100 1821 136 76 1964 175 182 667 708 724 1832 747 741 736 2192 745 732 155 148 1679 1628 1754 524 2232 683 1617 1790 1208 0\n2234 71 -54 -78 0 2227 1898 2224 2231 2220 2221 2180 2222 2090 2229 2176 2219 2233 1352 525 100 1821 136 76 1964 175 182 667 708 724 1832 747 741 736 2192 745 732 155 148 1679 1628 1754 683 1617 1790 1173 0\n2235 -54 -78 0 2227 2224 1898 2221 2220 2180 2231 2222 2090 2183 2229 2176 2219 1754 136 76 100 1628 1679 1964 1821 175 182 667 708 724 1832 747 741 736 2192 2233 1352 525 2234 1727 1786 1045 0\n2236 -6 -71 -78 0 2227 2090 2177 2182 2179 2183 2220 2226 2228 2224 2225 2231 2180 2222 2181 2221 2229 2176 2219 1727 124 136 2235 1341 715 721 1827 1832 745 732 1455 733 1838 736 1342 1551 1754 60 1964 2128 453 708 2129 1821 1675 698 1716 1721 1031 0\n2237 -71 -78 0 2227 2177 2182 2179 2183 2224 1898 2178 2222 2181 2221 2226 2231 2229 2176 2219 2235 1838 736 1342 1754 174 1727 2236 1677 1613 1603 698 1689 2129 341 708 1518 667 523 1099 0\n2238 6 -78 0 2227 2177 2182 2179 2224 1898 2178 2222 2181 2221 2231 2090 2229 2176 2219 2235 1341 715 721 1827 1832 745 732 136 2237 683 181 1455 1617 1838 736 1342 1754 1677 1613 1603 698 1698 2129 341 708 667 2078 193 1352 1834 1082 0\n2239 -78 0 2179 2182 2177 2090 2220 2226 2228 2224 2225 2231 2227 2180 2222 2181 2221 2176 2229 2219 136 1754 2235 1341 1342 1838 715 1551 736 721 1827 1832 745 732 733 1455 2237 683 1617 2238 60 1964 2128 1773 708 2129 1821 1675 698 1716 1721 1181 0\n2240 15 0 2239 2176 401 0\n2241 -181 0 2239 2230 2223 679 0\n2242 187 0 2239 2222 2230 2207 0\n2243 -190 0 2241 716 0\n2244 180 0 2241 1824 0\n2245 -85 0 2242 2231 2090 2180 1551 0\n2246 -192 0 2243 721 0\n2247 54 0 2244 2176 1341 0\n2248 -26 0 2244 2183 1382 0\n2249 197 0 2244 2221 2248 2183 2239 1971 0\n2250 -194 0 2246 1827 0\n2251 -47 0 2247 76 0\n2252 -62 0 2247 100 0\n2253 2 0 2247 2220 1628 0\n2254 6 0 2247 2221 1898 2224 1679 0\n2255 182 0 2249 732 0\n2256 183 0 2249 733 0\n2257 203 0 2250 1832 0\n2258 -177 0 2252 2180 1821 0\n2259 201 0 2257 747 0\n2260 178 0 2258 2242 708 0\n2261 199 0 2259 741 0\n2262 66 0 2260 2231 2251 2225 2245 2224 2256 2228 2255 2226 2128 0\n2263 185 0 2261 736 0\n2264 -74 0 2262 123 0\n2265 -84 0 2262 148 0\n2266 79 0 2262 2255 1455 0\n2267 45 0 2263 2247 2222 2192 0\n2268 89 0 2231 2265 2260 2227 2266 2262 2219 2247 2176 2267 2254 2229 2240 2253 667 1783 1518 1736 1803 982 0\n2269 -96 0 2268 193 0\n2270 -100 0 2268 202 0\n2271 18 0 2268 2090 1779 0\n2272 19 0 2268 2264 1788 0\n2273 99 0 2269 2176 2270 1761 0\n2274 98 0 2270 2269 2247 1715 0\n2275 0 2274 2273 2253 2271 2272 2219 2176 2267 2247 2229 2254 2266 2240 2262 2268 912 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.l) :=
(.branch 199
 (.branch 99
 (.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.branch 2
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨2, by decide⟩))))
 (.branch 4
 (.leaf (⟨3, by decide⟩))
 (.branch 5
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨6, by decide⟩))
 (.branch 8
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨8, by decide⟩))))
 (.branch 10
 (.leaf (⟨9, by decide⟩))
 (.branch 11
 (.leaf (⟨10, by decide⟩))
 (.leaf (⟨11, by decide⟩))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (⟨12, by decide⟩))
 (.branch 14
 (.leaf (⟨13, by decide⟩))
 (.leaf (⟨14, by decide⟩))))
 (.branch 16
 (.leaf (⟨15, by decide⟩))
 (.branch 17
 (.leaf (⟨16, by decide⟩))
 (.leaf (⟨17, by decide⟩)))))
 (.branch 21
 (.branch 19
 (.leaf (⟨18, by decide⟩))
 (.branch 20
 (.leaf (⟨19, by decide⟩))
 (.leaf (⟨20, by decide⟩))))
 (.branch 22
 (.leaf (⟨21, by decide⟩))
 (.branch 23
 (.leaf (⟨22, by decide⟩))
 (.leaf (⟨23, by decide⟩)))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf (⟨24, by decide⟩))
 (.branch 26
 (.leaf (⟨25, by decide⟩))
 (.leaf (⟨26, by decide⟩))))
 (.branch 28
 (.leaf (⟨27, by decide⟩))
 (.branch 29
 (.leaf (⟨28, by decide⟩))
 (.leaf (⟨29, by decide⟩)))))
 (.branch 33
 (.branch 31
 (.leaf (⟨30, by decide⟩))
 (.branch 32
 (.leaf (⟨31, by decide⟩))
 (.leaf (⟨32, by decide⟩))))
 (.branch 34
 (.leaf (⟨33, by decide⟩))
 (.branch 35
 (.leaf (⟨34, by decide⟩))
 (.leaf (⟨35, by decide⟩))))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf (⟨36, by decide⟩))
 (.branch 38
 (.leaf (⟨37, by decide⟩))
 (.leaf (⟨38, by decide⟩))))
 (.branch 40
 (.leaf (⟨39, by decide⟩))
 (.branch 41
 (.leaf (⟨40, by decide⟩))
 (.leaf (⟨41, by decide⟩)))))
 (.branch 45
 (.branch 43
 (.leaf (⟨42, by decide⟩))
 (.branch 44
 (.leaf (⟨43, by decide⟩))
 (.leaf (⟨44, by decide⟩))))
 (.branch 47
 (.branch 46
 (.leaf (⟨45, by decide⟩))
 (.leaf (⟨46, by decide⟩)))
 (.branch 48
 (.leaf (⟨47, by decide⟩))
 (.leaf (⟨48, by decide⟩))))))))
 (.branch 74
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf (⟨49, by decide⟩))
 (.branch 51
 (.leaf (⟨50, by decide⟩))
 (.leaf (⟨0, by decide⟩))))
 (.branch 53
 (.leaf (⟨0, by decide⟩))
 (.branch 54
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨0, by decide⟩)))))
 (.branch 58
 (.branch 56
 (.leaf (⟨0, by decide⟩))
 (.branch 57
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨0, by decide⟩))))
 (.branch 59
 (.leaf (⟨1, by decide⟩))
 (.branch 60
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨1, by decide⟩))))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf (⟨1, by decide⟩))
 (.branch 63
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨1, by decide⟩))))
 (.branch 65
 (.leaf (⟨1, by decide⟩))
 (.branch 66
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨2, by decide⟩)))))
 (.branch 70
 (.branch 68
 (.leaf (⟨2, by decide⟩))
 (.branch 69
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨2, by decide⟩))))
 (.branch 72
 (.branch 71
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨2, by decide⟩)))
 (.branch 73
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨3, by decide⟩)))))))
 (.branch 86
 (.branch 80
 (.branch 77
 (.branch 75
 (.leaf (⟨3, by decide⟩))
 (.branch 76
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
 (.branch 78
 (.leaf (⟨3, by decide⟩))
 (.branch 79
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨4, by decide⟩)))))
 (.branch 83
 (.branch 81
 (.leaf (⟨4, by decide⟩))
 (.branch 82
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨4, by decide⟩))))
 (.branch 84
 (.leaf (⟨4, by decide⟩))
 (.branch 85
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨4, by decide⟩))))))
 (.branch 92
 (.branch 89
 (.branch 87
 (.leaf (⟨5, by decide⟩))
 (.branch 88
 (.leaf (⟨5, by decide⟩))
 (.leaf (⟨5, by decide⟩))))
 (.branch 90
 (.leaf (⟨5, by decide⟩))
 (.branch 91
 (.leaf (⟨5, by decide⟩))
 (.leaf (⟨5, by decide⟩)))))
 (.branch 95
 (.branch 93
 (.leaf (⟨5, by decide⟩))
 (.branch 94
 (.leaf (⟨6, by decide⟩))
 (.leaf (⟨6, by decide⟩))))
 (.branch 97
 (.branch 96
 (.leaf (⟨6, by decide⟩))
 (.leaf (⟨6, by decide⟩)))
 (.branch 98
 (.leaf (⟨6, by decide⟩))
 (.leaf (⟨6, by decide⟩)))))))))
 (.branch 149
 (.branch 124
 (.branch 111
 (.branch 105
 (.branch 102
 (.branch 100
 (.leaf (⟨6, by decide⟩))
 (.branch 101
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨7, by decide⟩))))
 (.branch 103
 (.leaf (⟨7, by decide⟩))
 (.branch 104
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨7, by decide⟩)))))
 (.branch 108
 (.branch 106
 (.leaf (⟨7, by decide⟩))
 (.branch 107
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨8, by decide⟩))))
 (.branch 109
 (.leaf (⟨8, by decide⟩))
 (.branch 110
 (.leaf (⟨8, by decide⟩))
 (.leaf (⟨8, by decide⟩))))))
 (.branch 117
 (.branch 114
 (.branch 112
 (.leaf (⟨8, by decide⟩))
 (.branch 113
 (.leaf (⟨8, by decide⟩))
 (.leaf (⟨8, by decide⟩))))
 (.branch 115
 (.leaf (⟨9, by decide⟩))
 (.branch 116
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨9, by decide⟩)))))
 (.branch 120
 (.branch 118
 (.leaf (⟨9, by decide⟩))
 (.branch 119
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨9, by decide⟩))))
 (.branch 122
 (.branch 121
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨10, by decide⟩)))
 (.branch 123
 (.leaf (⟨10, by decide⟩))
 (.leaf (⟨10, by decide⟩)))))))
 (.branch 136
 (.branch 130
 (.branch 127
 (.branch 125
 (.leaf (⟨10, by decide⟩))
 (.branch 126
 (.leaf (⟨10, by decide⟩))
 (.leaf (⟨10, by decide⟩))))
 (.branch 128
 (.leaf (⟨10, by decide⟩))
 (.branch 129
 (.leaf (⟨11, by decide⟩))
 (.leaf (⟨11, by decide⟩)))))
 (.branch 133
 (.branch 131
 (.leaf (⟨11, by decide⟩))
 (.branch 132
 (.leaf (⟨11, by decide⟩))
 (.leaf (⟨11, by decide⟩))))
 (.branch 134
 (.leaf (⟨11, by decide⟩))
 (.branch 135
 (.leaf (⟨11, by decide⟩))
 (.leaf (⟨12, by decide⟩))))))
 (.branch 142
 (.branch 139
 (.branch 137
 (.leaf (⟨12, by decide⟩))
 (.branch 138
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨12, by decide⟩))))
 (.branch 140
 (.leaf (⟨12, by decide⟩))
 (.branch 141
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨12, by decide⟩)))))
 (.branch 145
 (.branch 143
 (.leaf (⟨13, by decide⟩))
 (.branch 144
 (.leaf (⟨13, by decide⟩))
 (.leaf (⟨13, by decide⟩))))
 (.branch 147
 (.branch 146
 (.leaf (⟨13, by decide⟩))
 (.leaf (⟨13, by decide⟩)))
 (.branch 148
 (.leaf (⟨13, by decide⟩))
 (.leaf (⟨13, by decide⟩))))))))
 (.branch 174
 (.branch 161
 (.branch 155
 (.branch 152
 (.branch 150
 (.leaf (⟨14, by decide⟩))
 (.branch 151
 (.leaf (⟨14, by decide⟩))
 (.leaf (⟨14, by decide⟩))))
 (.branch 153
 (.leaf (⟨14, by decide⟩))
 (.branch 154
 (.leaf (⟨14, by decide⟩))
 (.leaf (⟨14, by decide⟩)))))
 (.branch 158
 (.branch 156
 (.leaf (⟨14, by decide⟩))
 (.branch 157
 (.leaf (⟨15, by decide⟩))
 (.leaf (⟨15, by decide⟩))))
 (.branch 159
 (.leaf (⟨15, by decide⟩))
 (.branch 160
 (.leaf (⟨15, by decide⟩))
 (.leaf (⟨15, by decide⟩))))))
 (.branch 167
 (.branch 164
 (.branch 162
 (.leaf (⟨15, by decide⟩))
 (.branch 163
 (.leaf (⟨15, by decide⟩))
 (.leaf (⟨16, by decide⟩))))
 (.branch 165
 (.leaf (⟨16, by decide⟩))
 (.branch 166
 (.leaf (⟨16, by decide⟩))
 (.leaf (⟨16, by decide⟩)))))
 (.branch 170
 (.branch 168
 (.leaf (⟨16, by decide⟩))
 (.branch 169
 (.leaf (⟨16, by decide⟩))
 (.leaf (⟨16, by decide⟩))))
 (.branch 172
 (.branch 171
 (.leaf (⟨17, by decide⟩))
 (.leaf (⟨17, by decide⟩)))
 (.branch 173
 (.leaf (⟨17, by decide⟩))
 (.leaf (⟨17, by decide⟩)))))))
 (.branch 186
 (.branch 180
 (.branch 177
 (.branch 175
 (.leaf (⟨17, by decide⟩))
 (.branch 176
 (.leaf (⟨17, by decide⟩))
 (.leaf (⟨17, by decide⟩))))
 (.branch 178
 (.leaf (⟨18, by decide⟩))
 (.branch 179
 (.leaf (⟨18, by decide⟩))
 (.leaf (⟨18, by decide⟩)))))
 (.branch 183
 (.branch 181
 (.leaf (⟨18, by decide⟩))
 (.branch 182
 (.leaf (⟨18, by decide⟩))
 (.leaf (⟨18, by decide⟩))))
 (.branch 184
 (.leaf (⟨18, by decide⟩))
 (.branch 185
 (.leaf (⟨19, by decide⟩))
 (.leaf (⟨19, by decide⟩))))))
 (.branch 192
 (.branch 189
 (.branch 187
 (.leaf (⟨19, by decide⟩))
 (.branch 188
 (.leaf (⟨19, by decide⟩))
 (.leaf (⟨19, by decide⟩))))
 (.branch 190
 (.leaf (⟨19, by decide⟩))
 (.branch 191
 (.leaf (⟨19, by decide⟩))
 (.leaf (⟨20, by decide⟩)))))
 (.branch 195
 (.branch 193
 (.leaf (⟨20, by decide⟩))
 (.branch 194
 (.leaf (⟨20, by decide⟩))
 (.leaf (⟨20, by decide⟩))))
 (.branch 197
 (.branch 196
 (.leaf (⟨20, by decide⟩))
 (.leaf (⟨20, by decide⟩)))
 (.branch 198
 (.leaf (⟨20, by decide⟩))
 (.leaf (⟨21, by decide⟩))))))))))
 (.branch 298
 (.branch 248
 (.branch 223
 (.branch 211
 (.branch 205
 (.branch 202
 (.branch 200
 (.leaf (⟨21, by decide⟩))
 (.branch 201
 (.leaf (⟨21, by decide⟩))
 (.leaf (⟨21, by decide⟩))))
 (.branch 203
 (.leaf (⟨21, by decide⟩))
 (.branch 204
 (.leaf (⟨21, by decide⟩))
 (.leaf (⟨21, by decide⟩)))))
 (.branch 208
 (.branch 206
 (.leaf (⟨22, by decide⟩))
 (.branch 207
 (.leaf (⟨22, by decide⟩))
 (.leaf (⟨22, by decide⟩))))
 (.branch 209
 (.leaf (⟨22, by decide⟩))
 (.branch 210
 (.leaf (⟨22, by decide⟩))
 (.leaf (⟨22, by decide⟩))))))
 (.branch 217
 (.branch 214
 (.branch 212
 (.leaf (⟨22, by decide⟩))
 (.branch 213
 (.leaf (⟨23, by decide⟩))
 (.leaf (⟨23, by decide⟩))))
 (.branch 215
 (.leaf (⟨23, by decide⟩))
 (.branch 216
 (.leaf (⟨23, by decide⟩))
 (.leaf (⟨23, by decide⟩)))))
 (.branch 220
 (.branch 218
 (.leaf (⟨23, by decide⟩))
 (.branch 219
 (.leaf (⟨23, by decide⟩))
 (.leaf (⟨24, by decide⟩))))
 (.branch 221
 (.leaf (⟨24, by decide⟩))
 (.branch 222
 (.leaf (⟨24, by decide⟩))
 (.leaf (⟨24, by decide⟩)))))))
 (.branch 235
 (.branch 229
 (.branch 226
 (.branch 224
 (.leaf (⟨24, by decide⟩))
 (.branch 225
 (.leaf (⟨24, by decide⟩))
 (.leaf (⟨24, by decide⟩))))
 (.branch 227
 (.leaf (⟨25, by decide⟩))
 (.branch 228
 (.leaf (⟨25, by decide⟩))
 (.leaf (⟨25, by decide⟩)))))
 (.branch 232
 (.branch 230
 (.leaf (⟨25, by decide⟩))
 (.branch 231
 (.leaf (⟨25, by decide⟩))
 (.leaf (⟨25, by decide⟩))))
 (.branch 233
 (.leaf (⟨25, by decide⟩))
 (.branch 234
 (.leaf (⟨26, by decide⟩))
 (.leaf (⟨26, by decide⟩))))))
 (.branch 241
 (.branch 238
 (.branch 236
 (.leaf (⟨26, by decide⟩))
 (.branch 237
 (.leaf (⟨26, by decide⟩))
 (.leaf (⟨26, by decide⟩))))
 (.branch 239
 (.leaf (⟨26, by decide⟩))
 (.branch 240
 (.leaf (⟨26, by decide⟩))
 (.leaf (⟨27, by decide⟩)))))
 (.branch 244
 (.branch 242
 (.leaf (⟨27, by decide⟩))
 (.branch 243
 (.leaf (⟨27, by decide⟩))
 (.leaf (⟨27, by decide⟩))))
 (.branch 246
 (.branch 245
 (.leaf (⟨27, by decide⟩))
 (.leaf (⟨27, by decide⟩)))
 (.branch 247
 (.leaf (⟨27, by decide⟩))
 (.leaf (⟨28, by decide⟩))))))))
 (.branch 273
 (.branch 260
 (.branch 254
 (.branch 251
 (.branch 249
 (.leaf (⟨28, by decide⟩))
 (.branch 250
 (.leaf (⟨28, by decide⟩))
 (.leaf (⟨28, by decide⟩))))
 (.branch 252
 (.leaf (⟨28, by decide⟩))
 (.branch 253
 (.leaf (⟨28, by decide⟩))
 (.leaf (⟨28, by decide⟩)))))
 (.branch 257
 (.branch 255
 (.leaf (⟨29, by decide⟩))
 (.branch 256
 (.leaf (⟨29, by decide⟩))
 (.leaf (⟨29, by decide⟩))))
 (.branch 258
 (.leaf (⟨29, by decide⟩))
 (.branch 259
 (.leaf (⟨29, by decide⟩))
 (.leaf (⟨29, by decide⟩))))))
 (.branch 266
 (.branch 263
 (.branch 261
 (.leaf (⟨29, by decide⟩))
 (.branch 262
 (.leaf (⟨30, by decide⟩))
 (.leaf (⟨30, by decide⟩))))
 (.branch 264
 (.leaf (⟨30, by decide⟩))
 (.branch 265
 (.leaf (⟨30, by decide⟩))
 (.leaf (⟨30, by decide⟩)))))
 (.branch 269
 (.branch 267
 (.leaf (⟨30, by decide⟩))
 (.branch 268
 (.leaf (⟨30, by decide⟩))
 (.leaf (⟨31, by decide⟩))))
 (.branch 271
 (.branch 270
 (.leaf (⟨31, by decide⟩))
 (.leaf (⟨31, by decide⟩)))
 (.branch 272
 (.leaf (⟨31, by decide⟩))
 (.leaf (⟨31, by decide⟩)))))))
 (.branch 285
 (.branch 279
 (.branch 276
 (.branch 274
 (.leaf (⟨31, by decide⟩))
 (.branch 275
 (.leaf (⟨31, by decide⟩))
 (.leaf (⟨32, by decide⟩))))
 (.branch 277
 (.leaf (⟨32, by decide⟩))
 (.branch 278
 (.leaf (⟨32, by decide⟩))
 (.leaf (⟨32, by decide⟩)))))
 (.branch 282
 (.branch 280
 (.leaf (⟨32, by decide⟩))
 (.branch 281
 (.leaf (⟨32, by decide⟩))
 (.leaf (⟨32, by decide⟩))))
 (.branch 283
 (.leaf (⟨33, by decide⟩))
 (.branch 284
 (.leaf (⟨33, by decide⟩))
 (.leaf (⟨33, by decide⟩))))))
 (.branch 291
 (.branch 288
 (.branch 286
 (.leaf (⟨33, by decide⟩))
 (.branch 287
 (.leaf (⟨33, by decide⟩))
 (.leaf (⟨33, by decide⟩))))
 (.branch 289
 (.leaf (⟨33, by decide⟩))
 (.branch 290
 (.leaf (⟨34, by decide⟩))
 (.leaf (⟨34, by decide⟩)))))
 (.branch 294
 (.branch 292
 (.leaf (⟨34, by decide⟩))
 (.branch 293
 (.leaf (⟨34, by decide⟩))
 (.leaf (⟨34, by decide⟩))))
 (.branch 296
 (.branch 295
 (.leaf (⟨34, by decide⟩))
 (.leaf (⟨34, by decide⟩)))
 (.branch 297
 (.leaf (⟨35, by decide⟩))
 (.leaf (⟨35, by decide⟩)))))))))
 (.branch 348
 (.branch 323
 (.branch 310
 (.branch 304
 (.branch 301
 (.branch 299
 (.leaf (⟨35, by decide⟩))
 (.branch 300
 (.leaf (⟨35, by decide⟩))
 (.leaf (⟨35, by decide⟩))))
 (.branch 302
 (.leaf (⟨35, by decide⟩))
 (.branch 303
 (.leaf (⟨35, by decide⟩))
 (.leaf (⟨36, by decide⟩)))))
 (.branch 307
 (.branch 305
 (.leaf (⟨36, by decide⟩))
 (.branch 306
 (.leaf (⟨36, by decide⟩))
 (.leaf (⟨36, by decide⟩))))
 (.branch 308
 (.leaf (⟨36, by decide⟩))
 (.branch 309
 (.leaf (⟨36, by decide⟩))
 (.leaf (⟨36, by decide⟩))))))
 (.branch 316
 (.branch 313
 (.branch 311
 (.leaf (⟨37, by decide⟩))
 (.branch 312
 (.leaf (⟨37, by decide⟩))
 (.leaf (⟨37, by decide⟩))))
 (.branch 314
 (.leaf (⟨37, by decide⟩))
 (.branch 315
 (.leaf (⟨37, by decide⟩))
 (.leaf (⟨37, by decide⟩)))))
 (.branch 319
 (.branch 317
 (.leaf (⟨37, by decide⟩))
 (.branch 318
 (.leaf (⟨38, by decide⟩))
 (.leaf (⟨38, by decide⟩))))
 (.branch 321
 (.branch 320
 (.leaf (⟨38, by decide⟩))
 (.leaf (⟨38, by decide⟩)))
 (.branch 322
 (.leaf (⟨38, by decide⟩))
 (.leaf (⟨38, by decide⟩)))))))
 (.branch 335
 (.branch 329
 (.branch 326
 (.branch 324
 (.leaf (⟨38, by decide⟩))
 (.branch 325
 (.leaf (⟨39, by decide⟩))
 (.leaf (⟨39, by decide⟩))))
 (.branch 327
 (.leaf (⟨39, by decide⟩))
 (.branch 328
 (.leaf (⟨39, by decide⟩))
 (.leaf (⟨39, by decide⟩)))))
 (.branch 332
 (.branch 330
 (.leaf (⟨39, by decide⟩))
 (.branch 331
 (.leaf (⟨39, by decide⟩))
 (.leaf (⟨40, by decide⟩))))
 (.branch 333
 (.leaf (⟨40, by decide⟩))
 (.branch 334
 (.leaf (⟨40, by decide⟩))
 (.leaf (⟨40, by decide⟩))))))
 (.branch 341
 (.branch 338
 (.branch 336
 (.leaf (⟨40, by decide⟩))
 (.branch 337
 (.leaf (⟨40, by decide⟩))
 (.leaf (⟨40, by decide⟩))))
 (.branch 339
 (.leaf (⟨41, by decide⟩))
 (.branch 340
 (.leaf (⟨41, by decide⟩))
 (.leaf (⟨41, by decide⟩)))))
 (.branch 344
 (.branch 342
 (.leaf (⟨41, by decide⟩))
 (.branch 343
 (.leaf (⟨41, by decide⟩))
 (.leaf (⟨41, by decide⟩))))
 (.branch 346
 (.branch 345
 (.leaf (⟨41, by decide⟩))
 (.leaf (⟨42, by decide⟩)))
 (.branch 347
 (.leaf (⟨42, by decide⟩))
 (.leaf (⟨42, by decide⟩))))))))
 (.branch 373
 (.branch 360
 (.branch 354
 (.branch 351
 (.branch 349
 (.leaf (⟨42, by decide⟩))
 (.branch 350
 (.leaf (⟨42, by decide⟩))
 (.leaf (⟨42, by decide⟩))))
 (.branch 352
 (.leaf (⟨42, by decide⟩))
 (.branch 353
 (.leaf (⟨43, by decide⟩))
 (.leaf (⟨43, by decide⟩)))))
 (.branch 357
 (.branch 355
 (.leaf (⟨43, by decide⟩))
 (.branch 356
 (.leaf (⟨43, by decide⟩))
 (.leaf (⟨43, by decide⟩))))
 (.branch 358
 (.leaf (⟨43, by decide⟩))
 (.branch 359
 (.leaf (⟨43, by decide⟩))
 (.leaf (⟨44, by decide⟩))))))
 (.branch 366
 (.branch 363
 (.branch 361
 (.leaf (⟨44, by decide⟩))
 (.branch 362
 (.leaf (⟨44, by decide⟩))
 (.leaf (⟨44, by decide⟩))))
 (.branch 364
 (.leaf (⟨44, by decide⟩))
 (.branch 365
 (.leaf (⟨44, by decide⟩))
 (.leaf (⟨44, by decide⟩)))))
 (.branch 369
 (.branch 367
 (.leaf (⟨45, by decide⟩))
 (.branch 368
 (.leaf (⟨45, by decide⟩))
 (.leaf (⟨45, by decide⟩))))
 (.branch 371
 (.branch 370
 (.leaf (⟨45, by decide⟩))
 (.leaf (⟨45, by decide⟩)))
 (.branch 372
 (.leaf (⟨45, by decide⟩))
 (.leaf (⟨45, by decide⟩)))))))
 (.branch 385
 (.branch 379
 (.branch 376
 (.branch 374
 (.leaf (⟨46, by decide⟩))
 (.branch 375
 (.leaf (⟨46, by decide⟩))
 (.leaf (⟨46, by decide⟩))))
 (.branch 377
 (.leaf (⟨46, by decide⟩))
 (.branch 378
 (.leaf (⟨46, by decide⟩))
 (.leaf (⟨46, by decide⟩)))))
 (.branch 382
 (.branch 380
 (.leaf (⟨46, by decide⟩))
 (.branch 381
 (.leaf (⟨47, by decide⟩))
 (.leaf (⟨48, by decide⟩))))
 (.branch 383
 (.leaf (⟨48, by decide⟩))
 (.branch 384
 (.leaf (⟨48, by decide⟩))
 (.leaf (⟨49, by decide⟩))))))
 (.branch 391
 (.branch 388
 (.branch 386
 (.leaf (⟨49, by decide⟩))
 (.branch 387
 (.leaf (⟨49, by decide⟩))
 (.leaf (⟨49, by decide⟩))))
 (.branch 389
 (.leaf (⟨49, by decide⟩))
 (.branch 390
 (.leaf (⟨49, by decide⟩))
 (.leaf (⟨49, by decide⟩)))))
 (.branch 394
 (.branch 392
 (.leaf (⟨50, by decide⟩))
 (.branch 393
 (.leaf (⟨50, by decide⟩))
 (.leaf (⟨50, by decide⟩))))
 (.branch 396
 (.branch 395
 (.leaf (⟨50, by decide⟩))
 (.leaf (⟨50, by decide⟩)))
 (.branch 397
 (.leaf (⟨50, by decide⟩))
 (.leaf (⟨50, by decide⟩)))))))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.g)) :=
(.branch 199
 (.branch 99
 (.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([]))
 (.branch 2
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 4
 (.leaf ([]))
 (.branch 5
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 9
 (.branch 7
 (.leaf ([]))
 (.branch 8
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 10
 (.leaf ([]))
 (.branch 11
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ([]))
 (.branch 14
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 16
 (.leaf ([]))
 (.branch 17
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 21
 (.branch 19
 (.leaf ([]))
 (.branch 20
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 22
 (.leaf ([]))
 (.branch 23
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ([]))
 (.branch 26
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 28
 (.leaf ([]))
 (.branch 29
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 33
 (.branch 31
 (.leaf ([]))
 (.branch 32
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 34
 (.leaf ([]))
 (.branch 35
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ([]))
 (.branch 38
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 40
 (.leaf ([]))
 (.branch 41
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 45
 (.branch 43
 (.leaf ([]))
 (.branch 44
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 47
 (.branch 46
 (.leaf ([]))
 (.leaf ([])))
 (.branch 48
 (.leaf ([]))
 (.leaf ([]))))))))
 (.branch 74
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf ([]))
 (.branch 51
 (.leaf ([]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 53
 (.leaf ([⟨2, by decide⟩]))
 (.branch 54
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩])))))
 (.branch 58
 (.branch 56
 (.leaf ([⟨5, by decide⟩]))
 (.branch 57
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))
 (.branch 59
 (.leaf ([⟨1, by decide⟩]))
 (.branch 60
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf ([⟨4, by decide⟩]))
 (.branch 63
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))
 (.branch 65
 (.leaf ([⟨7, by decide⟩]))
 (.branch 66
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))))
 (.branch 70
 (.branch 68
 (.leaf ([⟨3, by decide⟩]))
 (.branch 69
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))
 (.branch 72
 (.branch 71
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩])))
 (.branch 73
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))))))
 (.branch 86
 (.branch 80
 (.branch 77
 (.branch 75
 (.leaf ([⟨3, by decide⟩]))
 (.branch 76
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))
 (.branch 78
 (.leaf ([⟨6, by decide⟩]))
 (.branch 79
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 83
 (.branch 81
 (.leaf ([⟨2, by decide⟩]))
 (.branch 82
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 84
 (.leaf ([⟨5, by decide⟩]))
 (.branch 85
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))))
 (.branch 92
 (.branch 89
 (.branch 87
 (.leaf ([⟨1, by decide⟩]))
 (.branch 88
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 90
 (.leaf ([⟨4, by decide⟩]))
 (.branch 91
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩])))))
 (.branch 95
 (.branch 93
 (.leaf ([⟨7, by decide⟩]))
 (.branch 94
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))
 (.branch 97
 (.branch 96
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩])))
 (.branch 98
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩])))))))))
 (.branch 149
 (.branch 124
 (.branch 111
 (.branch 105
 (.branch 102
 (.branch 100
 (.leaf ([⟨7, by decide⟩]))
 (.branch 101
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))
 (.branch 103
 (.leaf ([⟨3, by decide⟩]))
 (.branch 104
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩])))))
 (.branch 108
 (.branch 106
 (.leaf ([⟨6, by decide⟩]))
 (.branch 107
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 109
 (.leaf ([⟨2, by decide⟩]))
 (.branch 110
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))))
 (.branch 117
 (.branch 114
 (.branch 112
 (.leaf ([⟨5, by decide⟩]))
 (.branch 113
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))
 (.branch 115
 (.leaf ([⟨1, by decide⟩]))
 (.branch 116
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))))
 (.branch 120
 (.branch 118
 (.leaf ([⟨4, by decide⟩]))
 (.branch 119
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))
 (.branch 122
 (.branch 121
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 123
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))))))
 (.branch 136
 (.branch 130
 (.branch 127
 (.branch 125
 (.leaf ([⟨4, by decide⟩]))
 (.branch 126
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))
 (.branch 128
 (.leaf ([⟨7, by decide⟩]))
 (.branch 129
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))))
 (.branch 133
 (.branch 131
 (.leaf ([⟨3, by decide⟩]))
 (.branch 132
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))
 (.branch 134
 (.leaf ([⟨6, by decide⟩]))
 (.branch 135
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 142
 (.branch 139
 (.branch 137
 (.leaf ([⟨2, by decide⟩]))
 (.branch 138
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 140
 (.leaf ([⟨5, by decide⟩]))
 (.branch 141
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩])))))
 (.branch 145
 (.branch 143
 (.leaf ([⟨1, by decide⟩]))
 (.branch 144
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 147
 (.branch 146
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩])))
 (.branch 148
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))))))
 (.branch 174
 (.branch 161
 (.branch 155
 (.branch 152
 (.branch 150
 (.leaf ([⟨1, by decide⟩]))
 (.branch 151
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 153
 (.leaf ([⟨4, by decide⟩]))
 (.branch 154
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩])))))
 (.branch 158
 (.branch 156
 (.leaf ([⟨7, by decide⟩]))
 (.branch 157
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))
 (.branch 159
 (.leaf ([⟨3, by decide⟩]))
 (.branch 160
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))))
 (.branch 167
 (.branch 164
 (.branch 162
 (.leaf ([⟨6, by decide⟩]))
 (.branch 163
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 165
 (.leaf ([⟨2, by decide⟩]))
 (.branch 166
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩])))))
 (.branch 170
 (.branch 168
 (.leaf ([⟨5, by decide⟩]))
 (.branch 169
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))
 (.branch 172
 (.branch 171
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))
 (.branch 173
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩])))))))
 (.branch 186
 (.branch 180
 (.branch 177
 (.branch 175
 (.leaf ([⟨5, by decide⟩]))
 (.branch 176
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))
 (.branch 178
 (.leaf ([⟨1, by decide⟩]))
 (.branch 179
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))))
 (.branch 183
 (.branch 181
 (.leaf ([⟨4, by decide⟩]))
 (.branch 182
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))
 (.branch 184
 (.leaf ([⟨7, by decide⟩]))
 (.branch 185
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))))
 (.branch 192
 (.branch 189
 (.branch 187
 (.leaf ([⟨3, by decide⟩]))
 (.branch 188
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))
 (.branch 190
 (.leaf ([⟨6, by decide⟩]))
 (.branch 191
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 195
 (.branch 193
 (.leaf ([⟨2, by decide⟩]))
 (.branch 194
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 197
 (.branch 196
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩])))
 (.branch 198
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))))))
 (.branch 298
 (.branch 248
 (.branch 223
 (.branch 211
 (.branch 205
 (.branch 202
 (.branch 200
 (.leaf ([⟨2, by decide⟩]))
 (.branch 201
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 203
 (.leaf ([⟨5, by decide⟩]))
 (.branch 204
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩])))))
 (.branch 208
 (.branch 206
 (.leaf ([⟨1, by decide⟩]))
 (.branch 207
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 209
 (.leaf ([⟨4, by decide⟩]))
 (.branch 210
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))))
 (.branch 217
 (.branch 214
 (.branch 212
 (.leaf ([⟨7, by decide⟩]))
 (.branch 213
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))
 (.branch 215
 (.leaf ([⟨3, by decide⟩]))
 (.branch 216
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩])))))
 (.branch 220
 (.branch 218
 (.leaf ([⟨6, by decide⟩]))
 (.branch 219
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 221
 (.leaf ([⟨2, by decide⟩]))
 (.branch 222
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩])))))))
 (.branch 235
 (.branch 229
 (.branch 226
 (.branch 224
 (.leaf ([⟨5, by decide⟩]))
 (.branch 225
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))
 (.branch 227
 (.leaf ([⟨1, by decide⟩]))
 (.branch 228
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))))
 (.branch 232
 (.branch 230
 (.leaf ([⟨4, by decide⟩]))
 (.branch 231
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))
 (.branch 233
 (.leaf ([⟨7, by decide⟩]))
 (.branch 234
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))))
 (.branch 241
 (.branch 238
 (.branch 236
 (.leaf ([⟨3, by decide⟩]))
 (.branch 237
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))
 (.branch 239
 (.leaf ([⟨6, by decide⟩]))
 (.branch 240
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 244
 (.branch 242
 (.leaf ([⟨2, by decide⟩]))
 (.branch 243
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 246
 (.branch 245
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩])))
 (.branch 247
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))))
 (.branch 273
 (.branch 260
 (.branch 254
 (.branch 251
 (.branch 249
 (.leaf ([⟨2, by decide⟩]))
 (.branch 250
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 252
 (.leaf ([⟨5, by decide⟩]))
 (.branch 253
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩])))))
 (.branch 257
 (.branch 255
 (.leaf ([⟨1, by decide⟩]))
 (.branch 256
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 258
 (.leaf ([⟨4, by decide⟩]))
 (.branch 259
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))))
 (.branch 266
 (.branch 263
 (.branch 261
 (.leaf ([⟨7, by decide⟩]))
 (.branch 262
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))
 (.branch 264
 (.leaf ([⟨3, by decide⟩]))
 (.branch 265
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩])))))
 (.branch 269
 (.branch 267
 (.leaf ([⟨6, by decide⟩]))
 (.branch 268
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 271
 (.branch 270
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))
 (.branch 272
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩])))))))
 (.branch 285
 (.branch 279
 (.branch 276
 (.branch 274
 (.leaf ([⟨6, by decide⟩]))
 (.branch 275
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 277
 (.leaf ([⟨2, by decide⟩]))
 (.branch 278
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩])))))
 (.branch 282
 (.branch 280
 (.leaf ([⟨5, by decide⟩]))
 (.branch 281
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))
 (.branch 283
 (.leaf ([⟨1, by decide⟩]))
 (.branch 284
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))))
 (.branch 291
 (.branch 288
 (.branch 286
 (.leaf ([⟨4, by decide⟩]))
 (.branch 287
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))
 (.branch 289
 (.leaf ([⟨7, by decide⟩]))
 (.branch 290
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))))
 (.branch 294
 (.branch 292
 (.leaf ([⟨3, by decide⟩]))
 (.branch 293
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))
 (.branch 296
 (.branch 295
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩])))
 (.branch 297
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))))))))
 (.branch 348
 (.branch 323
 (.branch 310
 (.branch 304
 (.branch 301
 (.branch 299
 (.leaf ([⟨3, by decide⟩]))
 (.branch 300
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))
 (.branch 302
 (.leaf ([⟨6, by decide⟩]))
 (.branch 303
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 307
 (.branch 305
 (.leaf ([⟨2, by decide⟩]))
 (.branch 306
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 308
 (.leaf ([⟨5, by decide⟩]))
 (.branch 309
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))))
 (.branch 316
 (.branch 313
 (.branch 311
 (.leaf ([⟨1, by decide⟩]))
 (.branch 312
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 314
 (.leaf ([⟨4, by decide⟩]))
 (.branch 315
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩])))))
 (.branch 319
 (.branch 317
 (.leaf ([⟨7, by decide⟩]))
 (.branch 318
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))
 (.branch 321
 (.branch 320
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩])))
 (.branch 322
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩])))))))
 (.branch 335
 (.branch 329
 (.branch 326
 (.branch 324
 (.leaf ([⟨7, by decide⟩]))
 (.branch 325
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))
 (.branch 327
 (.leaf ([⟨3, by decide⟩]))
 (.branch 328
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩])))))
 (.branch 332
 (.branch 330
 (.leaf ([⟨6, by decide⟩]))
 (.branch 331
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 333
 (.leaf ([⟨2, by decide⟩]))
 (.branch 334
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))))
 (.branch 341
 (.branch 338
 (.branch 336
 (.leaf ([⟨5, by decide⟩]))
 (.branch 337
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))
 (.branch 339
 (.leaf ([⟨1, by decide⟩]))
 (.branch 340
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))))
 (.branch 344
 (.branch 342
 (.leaf ([⟨4, by decide⟩]))
 (.branch 343
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))
 (.branch 346
 (.branch 345
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 347
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))))))
 (.branch 373
 (.branch 360
 (.branch 354
 (.branch 351
 (.branch 349
 (.leaf ([⟨4, by decide⟩]))
 (.branch 350
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))
 (.branch 352
 (.leaf ([⟨7, by decide⟩]))
 (.branch 353
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))))
 (.branch 357
 (.branch 355
 (.leaf ([⟨3, by decide⟩]))
 (.branch 356
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))
 (.branch 358
 (.leaf ([⟨6, by decide⟩]))
 (.branch 359
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 366
 (.branch 363
 (.branch 361
 (.leaf ([⟨2, by decide⟩]))
 (.branch 362
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 364
 (.leaf ([⟨5, by decide⟩]))
 (.branch 365
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩])))))
 (.branch 369
 (.branch 367
 (.leaf ([⟨1, by decide⟩]))
 (.branch 368
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 371
 (.branch 370
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩])))
 (.branch 372
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩])))))))
 (.branch 385
 (.branch 379
 (.branch 376
 (.branch 374
 (.leaf ([⟨1, by decide⟩]))
 (.branch 375
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 377
 (.leaf ([⟨4, by decide⟩]))
 (.branch 378
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩])))))
 (.branch 382
 (.branch 380
 (.leaf ([⟨7, by decide⟩]))
 (.branch 381
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 383
 (.leaf ([⟨4, by decide⟩]))
 (.branch 384
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 391
 (.branch 388
 (.branch 386
 (.leaf ([⟨2, by decide⟩]))
 (.branch 387
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 389
 (.leaf ([⟨5, by decide⟩]))
 (.branch 390
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩])))))
 (.branch 394
 (.branch 392
 (.leaf ([⟨1, by decide⟩]))
 (.branch 393
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 396
 (.branch 395
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩])))
 (.branch 397
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩])))))))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "23c4eac671aa69999655a8e63a4e53a2e47bc1e27498e539716a59959555635a358d9354d8751db0ea398d9354d33a2d8b92d4b8ad2ba1d8791d4789ca719d1725c5783d0f23c4fb122c0f1c24683a318360b81eb05c18a5190e685914c5894358342d0758350cc344c3342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "24936db6da49b4924da4d349369269a492492492492249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 61), (facetIndex 73), (facetIndex 78)]))
 (.leaf ([(facetIndex 50), (facetIndex 56), (facetIndex 74), (facetIndex 91)])))
 (.branch 3
 (.leaf ([(facetIndex 63), (facetIndex 68), (facetIndex 75), (facetIndex 92)]))
 (.leaf ([(facetIndex 38), (facetIndex 42), (facetIndex 46), (facetIndex 48), (facetIndex 62), (facetIndex 79), (facetIndex 89)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 52), (facetIndex 54), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 39), (facetIndex 45), (facetIndex 47), (facetIndex 49), (facetIndex 65), (facetIndex 67), (facetIndex 71), (facetIndex 72)])))
 (.branch 7
 (.leaf ([(facetIndex 51), (facetIndex 80), (facetIndex 90)]))
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 40), (facetIndex 41), (facetIndex 43), (facetIndex 44)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2398000006600445a02a284c0121104c6baefeffaffz1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 53), (facetIndex 55), (facetIndex 59), (facetIndex 60)])))
 (.branch 3
 (.leaf ([(facetIndex 64), (facetIndex 66), (facetIndex 69), (facetIndex 70)]))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 82), (facetIndex 84), (facetIndex 87), (facetIndex 88)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "48dc718000000090082001200208z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [2]
def grouped3_0016 : List Nat := [2, 3, 4]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4]
def grouped3_0019 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record005" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record005" "{\"ridges\":[[76,840],[77,904],[81,332],[83,396],[85,340],[86,404]],\"owners\":[[81,332,[64],[]],[83,396,[66],[]],[85,340,[69],[]],[86,404,[70],[]],[76,840,[],[]],[77,904,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-6,-5],[-7,-5],[-8,-5],[-9,-5],[-11,-1],[-11,-2],[-11,-3],[-11,-4],[-11,-10],[-12,-1],[-12,-2],[-12,-3],[-12,-4],[-12,-10],[-13,-1],[-13,-2],[-13,-3],[-13,-4],[-13,-10],[-14,-1],[-14,-2],[-14,-3],[-14,-4],[-14,-10],[-17,-11],[-17,-12],[-17,-13],[-17,-14],[-18,-6],[-18,-7],[-18,-8],[-18,-9],[-23,-11],[-23,-12],[-23,-13],[-23,-14],[-24,-6],[-24,-7],[-24,-8],[-24,-9],[-19,11],[-20,12],[-21,13],[-22,14],[-15],[-16],[-25,1,2,3,4,10,17,23],[-26,5,18,24],[-27,25],[-28,27],[-29,26],[-30,29],[-31,28],[-31,30],[31],[-32,15,16],[-33,6,7,8,9],[-34,11,12,13,14],[-11,34],[-12,34],[-13,34],[-14,34],[-35,19,20,21,22],[-36,32,33],[-37,35],[-38,34,37],[-39,36,38],[39]],\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":59,\"b\":51},{\"tag\":\"incompatible\",\"a\":60,\"b\":51},{\"tag\":\"incompatible\",\"a\":64,\"b\":38},{\"tag\":\"incompatible\",\"a\":64,\"b\":42},{\"tag\":\"incompatible\",\"a\":64,\"b\":46},{\"tag\":\"incompatible\",\"a\":64,\"b\":48},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":38},{\"tag\":\"incompatible\",\"a\":66,\"b\":42},{\"tag\":\"incompatible\",\"a\":66,\"b\":46},{\"tag\":\"incompatible\",\"a\":66,\"b\":48},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":38},{\"tag\":\"incompatible\",\"a\":69,\"b\":42},{\"tag\":\"incompatible\",\"a\":69,\"b\":46},{\"tag\":\"incompatible\",\"a\":69,\"b\":48},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":70,\"b\":38},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":70,\"b\":46},{\"tag\":\"incompatible\",\"a\":70,\"b\":48},{\"tag\":\"incompatible\",\"a\":70,\"b\":62},{\"tag\":\"incompatible\",\"a\":79,\"b\":64},{\"tag\":\"incompatible\",\"a\":79,\"b\":66},{\"tag\":\"incompatible\",\"a\":79,\"b\":69},{\"tag\":\"incompatible\",\"a\":79,\"b\":70},{\"tag\":\"incompatible\",\"a\":80,\"b\":53},{\"tag\":\"incompatible\",\"a\":80,\"b\":55},{\"tag\":\"incompatible\",\"a\":80,\"b\":59},{\"tag\":\"incompatible\",\"a\":80,\"b\":60},{\"tag\":\"incompatible\",\"a\":89,\"b\":64},{\"tag\":\"incompatible\",\"a\":89,\"b\":66},{\"tag\":\"incompatible\",\"a\":89,\"b\":69},{\"tag\":\"incompatible\",\"a\":89,\"b\":70},{\"tag\":\"incompatible\",\"a\":90,\"b\":53},{\"tag\":\"incompatible\",\"a\":90,\"b\":55},{\"tag\":\"incompatible\",\"a\":90,\"b\":59},{\"tag\":\"incompatible\",\"a\":90,\"b\":60},{\"tag\":\"mate\",\"ridge\":332,\"a\":81,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":396,\"a\":83,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":340,\"a\":85,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":404,\"a\":86,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":840,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":904,\"a\":77,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[38,42,46,48,62,79,89],\"full_literals\":[-25,1,2,3,4,10,17,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[51,80,90],\"full_literals\":[-26,5,18,24]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-27,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-28,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-31,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[76,77],\"full_literals\":[-32,15,16]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[53,55,59,60],\"full_literals\":[-33,6,7,8,9]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[64,66,69,70],\"full_literals\":[-34,11,12,13,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-11,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-12,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-13,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-14,34]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[81,83,85,86],\"full_literals\":[-35,19,20,21,22]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,35,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,34,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "p cnf 39 68\n-6 -5 0\n-7 -5 0\n-8 -5 0\n-9 -5 0\n-11 -1 0\n-11 -2 0\n-11 -3 0\n-11 -4 0\n-11 -10 0\n-12 -1 0\n-12 -2 0\n-12 -3 0\n-12 -4 0\n-12 -10 0\n-13 -1 0\n-13 -2 0\n-13 -3 0\n-13 -4 0\n-13 -10 0\n-14 -1 0\n-14 -2 0\n-14 -3 0\n-14 -4 0\n-14 -10 0\n-17 -11 0\n-17 -12 0\n-17 -13 0\n-17 -14 0\n-18 -6 0\n-18 -7 0\n-18 -8 0\n-18 -9 0\n-23 -11 0\n-23 -12 0\n-23 -13 0\n-23 -14 0\n-24 -6 0\n-24 -7 0\n-24 -8 0\n-24 -9 0\n-19 11 0\n-20 12 0\n-21 13 0\n-22 14 0\n-15 0\n-16 0\n-25 1 2 3 4 10 17 23 0\n-26 5 18 24 0\n-27 25 0\n-28 27 0\n-29 26 0\n-30 29 0\n-31 28 0\n-31 30 0\n31 0\n-32 15 16 0\n-33 6 7 8 9 0\n-34 11 12 13 14 0\n-11 34 0\n-12 34 0\n-13 34 0\n-14 34 0\n-35 19 20 21 22 0\n-36 32 33 0\n-37 35 0\n-38 34 37 0\n-39 36 38 0\n39 0\n"
  "69 28 0 55 53 0\n70 30 0 55 54 0\n71 27 0 69 50 0\n72 29 0 70 52 0\n73 25 0 71 49 0\n74 26 0 72 51 0\n75 -32 0 45 46 56 0\n76 -36 33 0 75 64 0\n77 -10 -34 0 9 14 19 24 58 0\n78 -23 -34 0 33 34 35 36 58 0\n79 -11 -34 0 73 78 77 5 6 7 8 25 47 0\n80 -12 -34 0 73 78 77 10 11 12 13 26 47 0\n81 -13 -34 0 73 78 77 15 16 17 18 27 47 0\n82 -34 0 73 77 78 79 80 81 58 20 21 22 23 28 47 0\n83 -11 0 82 59 0\n84 -12 0 82 60 0\n85 -13 0 82 61 0\n86 -14 0 82 62 0\n87 -19 0 83 41 0\n88 -20 0 84 42 0\n89 -21 0 85 43 0\n90 -22 0 86 44 0\n91 -35 0 90 89 87 88 63 0\n92 -37 0 91 65 0\n93 -38 0 92 82 66 0\n94 36 0 93 68 67 0\n95 33 0 94 76 0\n96 -18 0 95 29 30 31 32 57 0\n97 -5 0 95 1 2 3 4 57 0\n98 24 0 97 74 96 48 0\n99 -6 0 98 37 0\n100 -7 0 98 38 0\n101 -8 0 98 39 0\n102 -9 0 98 40 0\n103 0 101 100 99 95 102 57 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record005
