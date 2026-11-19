module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00031Frames
public import GraphInputsRow24Part00031Leaves
public import GraphInputsRow24Part00031Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f83d0ec370bc1f2b23cb2a3a8da2e87a39b16358b61d98e338ae1b89e1783e9c4f1ca4e9364b91e4e5c54d52d475534cd2b46d2745d0f72338f1334cb31cf0b32e2b4acab1ac9b16c3bc1cc729c6785d1725c570dc8f13c2f07cf03a0d4332322c8aa2590e23a311c4691550d1370388e130cd0b0ad0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "24936934d36d269269b49a6d369a49a69a69a49a4936936d2492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.branch 2
 (.leaf ([(facetIndex 1)]))
 (.leaf ([(facetIndex 2)]))))
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.leaf ([(facetIndex 8)]))))
 (.branch 10
 (.leaf ([(facetIndex 9)]))
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)]))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.branch 14
 (.leaf ([(facetIndex 13)]))
 (.leaf ([(facetIndex 14)]))))
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)])))))
 (.branch 21
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.leaf ([(facetIndex 20)]))))
 (.branch 23
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)])))
 (.branch 24
 (.leaf ([(facetIndex 23)]))
 (.leaf ([(facetIndex 24)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "18bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 25
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 37), (facetIndex 50)]))
 (.leaf ([(facetIndex 27), (facetIndex 54), (facetIndex 56), (facetIndex 58), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 60), (facetIndex 65), (facetIndex 70), (facetIndex 71)]))
 (.branch 4
 (.leaf ([(facetIndex 28), (facetIndex 74), (facetIndex 76), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 48), (facetIndex 80), (facetIndex 85), (facetIndex 89), (facetIndex 90)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 52)]))
 (.leaf ([(facetIndex 62), (facetIndex 81), (facetIndex 93), (facetIndex 95)])))
 (.branch 8
 (.leaf ([(facetIndex 68), (facetIndex 87), (facetIndex 94), (facetIndex 96)]))
 (.branch 9
 (.leaf ([(facetIndex 25), (facetIndex 29), (facetIndex 30), (facetIndex 31)]))
 (.leaf ([(facetIndex 26), (facetIndex 38), (facetIndex 41), (facetIndex 42)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "767600440704000640333030022070020060211010105000425055990090000008883198z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 63)]))
 (.branch 2
 (.leaf ([(facetIndex 69)]))
 (.leaf ([(facetIndex 82)]))))
 (.branch 4
 (.leaf ([(facetIndex 88)]))
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 36)]))
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 45)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 55), (facetIndex 57)]))
 (.branch 8
 (.leaf ([(facetIndex 51), (facetIndex 61), (facetIndex 66)]))
 (.leaf ([(facetIndex 53), (facetIndex 64), (facetIndex 67)]))))
 (.branch 10
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 75)]))
 (.branch 11
 (.leaf ([(facetIndex 79), (facetIndex 84), (facetIndex 91)]))
 (.leaf ([(facetIndex 83), (facetIndex 86), (facetIndex 92)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "ba0030b0ab200a000909900108708007000606080706000500005500444z22;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1, 2]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def grouped1_0005 : List Nat := [1]
def grouped1_0006 : List Nat := [1, 2]
def grouped1_0007 : List Nat := [2]
def grouped1_0008 : List Nat := [3]
def grouped1_0009 : List Nat := [3, 4, 5]
def grouped1_0010 : List Nat := [4]
def grouped1_0011 : List Nat := [4, 5]
def grouped1_0012 : List Nat := [5]
def grouped1_0013 : List Nat := [6]
def grouped1_0014 : List Nat := [6, 7, 8]
def grouped1_0015 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped1_0016 : List Nat := [7]
def grouped1_0017 : List Nat := [7, 8]
def grouped1_0018 : List Nat := [8]
def grouped1_0019 : List Nat := [9]
def grouped1_0020 : List Nat := [9, 10, 11]
def grouped1_0021 : List Nat := [10]
def grouped1_0022 : List Nat := [10, 11]
def grouped1_0023 : List Nat := [11]
def grouped1_0024 : List Nat := [12]
def grouped1_0025 : List Nat := [12, 13, 14]
def grouped1_0026 : List Nat := [12, 13, 14, 15, 16, 17]
def grouped1_0027 : List Nat := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
def grouped1_0028 : List Nat := [13]
def grouped1_0029 : List Nat := [13, 14]
def grouped1_0030 : List Nat := [14]
def grouped1_0031 : List Nat := [15]
def grouped1_0032 : List Nat := [15, 16, 17]
def grouped1_0033 : List Nat := [16]
def grouped1_0034 : List Nat := [16, 17]
def grouped1_0035 : List Nat := [17]
def grouped1_0036 : List Nat := [18, 19, 20]
def grouped1_0037 : List Nat := [18, 19, 20, 21, 22, 23, 24]
def grouped1_0038 : List Nat := [21]
def grouped1_0039 : List Nat := [21, 22]
def grouped1_0040 : List Nat := [21, 22, 23, 24]
def grouped1_0041 : List Nat := [22]
def grouped1_0042 : List Nat := [23]
def grouped1_0043 : List Nat := [23, 24]
def grouped1_0044 : List Nat := [24]
def grouped2_0045 : List Nat := [0]
def grouped2_0046 : List Nat := [0, 1]
def grouped2_0047 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0049 : List Nat := [1]
def grouped2_0050 : List Nat := [2]
def grouped2_0051 : List Nat := [2, 3, 4]
def grouped2_0052 : List Nat := [3]
def grouped2_0053 : List Nat := [3, 4]
def grouped2_0054 : List Nat := [4]
def grouped2_0055 : List Nat := [5]
def grouped2_0056 : List Nat := [5, 6]
def grouped2_0057 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0058 : List Nat := [6]
def grouped2_0059 : List Nat := [7]
def grouped2_0060 : List Nat := [7, 8, 9]
def grouped2_0061 : List Nat := [8]
def grouped2_0062 : List Nat := [8, 9]
def grouped2_0063 : List Nat := [9]
def grouped3_0064 : List Nat := [0]
def grouped3_0065 : List Nat := [0, 1, 2]
def grouped3_0066 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0068 : List Nat := [1]
def grouped3_0069 : List Nat := [1, 2]
def grouped3_0070 : List Nat := [2]
def grouped3_0071 : List Nat := [3]
def grouped3_0072 : List Nat := [3, 4, 5]
def grouped3_0073 : List Nat := [4]
def grouped3_0074 : List Nat := [4, 5]
def grouped3_0075 : List Nat := [5]
def grouped3_0076 : List Nat := [6]
def grouped3_0077 : List Nat := [6, 7, 8]
def grouped3_0078 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0079 : List Nat := [7]
def grouped3_0080 : List Nat := [7, 8]
def grouped3_0081 : List Nat := [8]
def grouped3_0082 : List Nat := [9]
def grouped3_0083 : List Nat := [9, 10, 11]
def grouped3_0084 : List Nat := [10]
def grouped3_0085 : List Nat := [10, 11]
def grouped3_0086 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_matrix_checked

def leafCount : Nat := 48
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 2), (facetIndex 10), (facetIndex 11), (facetIndex 24), (facetIndex 31), (facetIndex 50), (facetIndex 56), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 2), (facetIndex 10), (facetIndex 12), (facetIndex 21), (facetIndex 31), (facetIndex 50), (facetIndex 54), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 2), (facetIndex 12), (facetIndex 14), (facetIndex 24), (facetIndex 31), (facetIndex 50), (facetIndex 59), (facetIndex 60), (facetIndex 69), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 2), (facetIndex 11), (facetIndex 14), (facetIndex 21), (facetIndex 31), (facetIndex 50), (facetIndex 59), (facetIndex 65), (facetIndex 69), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 2), (facetIndex 11), (facetIndex 12), (facetIndex 21), (facetIndex 31), (facetIndex 50), (facetIndex 59), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 2), (facetIndex 11), (facetIndex 12), (facetIndex 24), (facetIndex 31), (facetIndex 50), (facetIndex 59), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 12), (facetIndex 24), (facetIndex 42), (facetIndex 52), (facetIndex 54), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 6), (facetIndex 11), (facetIndex 14), (facetIndex 21), (facetIndex 31), (facetIndex 37), (facetIndex 59), (facetIndex 65), (facetIndex 69), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 7), (facetIndex 12), (facetIndex 14), (facetIndex 21), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 60), (facetIndex 63), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 2), (facetIndex 16), (facetIndex 17), (facetIndex 24), (facetIndex 30), (facetIndex 50), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 4), (facetIndex 16), (facetIndex 18), (facetIndex 24), (facetIndex 41), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 74), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 6), (facetIndex 17), (facetIndex 20), (facetIndex 21), (facetIndex 30), (facetIndex 37), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 85), (facetIndex 88), (facetIndex 95)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 7), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 41), (facetIndex 46), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 80), (facetIndex 82), (facetIndex 96)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 11), (facetIndex 21), (facetIndex 42), (facetIndex 52), (facetIndex 56), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 6), (facetIndex 12), (facetIndex 14), (facetIndex 24), (facetIndex 31), (facetIndex 37), (facetIndex 59), (facetIndex 60), (facetIndex 69), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 14), (facetIndex 24), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 63), (facetIndex 65), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 2), (facetIndex 16), (facetIndex 18), (facetIndex 21), (facetIndex 30), (facetIndex 50), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 74), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 4), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 41), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 76), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 6), (facetIndex 18), (facetIndex 20), (facetIndex 24), (facetIndex 30), (facetIndex 37), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 80), (facetIndex 88), (facetIndex 93)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 7), (facetIndex 17), (facetIndex 20), (facetIndex 24), (facetIndex 41), (facetIndex 46), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 82), (facetIndex 85), (facetIndex 94)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 4), (facetIndex 11), (facetIndex 14), (facetIndex 24), (facetIndex 42), (facetIndex 52), (facetIndex 59), (facetIndex 63), (facetIndex 65), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 6), (facetIndex 10), (facetIndex 12), (facetIndex 21), (facetIndex 31), (facetIndex 37), (facetIndex 54), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 21), (facetIndex 42), (facetIndex 46), (facetIndex 56), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 2), (facetIndex 18), (facetIndex 20), (facetIndex 24), (facetIndex 30), (facetIndex 50), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 80), (facetIndex 88), (facetIndex 93)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 4), (facetIndex 17), (facetIndex 20), (facetIndex 24), (facetIndex 41), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 82), (facetIndex 85), (facetIndex 94)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 6), (facetIndex 16), (facetIndex 18), (facetIndex 21), (facetIndex 30), (facetIndex 37), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 74), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 7), (facetIndex 16), (facetIndex 17), (facetIndex 21), (facetIndex 41), (facetIndex 46), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 76), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leaf0027 : List (Fin data.count) := [(facetIndex 4), (facetIndex 12), (facetIndex 14), (facetIndex 21), (facetIndex 42), (facetIndex 52), (facetIndex 59), (facetIndex 60), (facetIndex 63), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0027_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0027 = true := by
  decide +kernel
theorem leaf0027_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0027 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0027_counts_checked
def leaf0028 : List (Fin data.count) := [(facetIndex 6), (facetIndex 10), (facetIndex 11), (facetIndex 24), (facetIndex 31), (facetIndex 37), (facetIndex 56), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0028_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0028 = true := by
  decide +kernel
theorem leaf0028_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0028 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0028_counts_checked
def leaf0029 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 12), (facetIndex 24), (facetIndex 42), (facetIndex 46), (facetIndex 54), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0029_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0029 = true := by
  decide +kernel
theorem leaf0029_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0029 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0029_counts_checked
def leaf0030 : List (Fin data.count) := [(facetIndex 2), (facetIndex 17), (facetIndex 20), (facetIndex 21), (facetIndex 30), (facetIndex 50), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 85), (facetIndex 88), (facetIndex 95)]
theorem leaf0030_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0030 = true := by
  decide +kernel
theorem leaf0030_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0030 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0030_counts_checked
def leaf0031 : List (Fin data.count) := [(facetIndex 4), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 41), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 80), (facetIndex 82), (facetIndex 96)]
theorem leaf0031_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0031 = true := by
  decide +kernel
theorem leaf0031_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0031 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0031_counts_checked
def leaf0032 : List (Fin data.count) := [(facetIndex 6), (facetIndex 16), (facetIndex 17), (facetIndex 24), (facetIndex 30), (facetIndex 37), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0032_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0032 = true := by
  decide +kernel
theorem leaf0032_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0032 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0032_counts_checked
def leaf0033 : List (Fin data.count) := [(facetIndex 7), (facetIndex 16), (facetIndex 18), (facetIndex 24), (facetIndex 41), (facetIndex 46), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 74), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0033_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0033 = true := by
  decide +kernel
theorem leaf0033_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0033 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0033_counts_checked
def leaf0034 : List (Fin data.count) := [(facetIndex 4), (facetIndex 11), (facetIndex 12), (facetIndex 21), (facetIndex 42), (facetIndex 52), (facetIndex 59), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0034_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0034 = true := by
  decide +kernel
theorem leaf0034_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0034 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0034_counts_checked
def leaf0035 : List (Fin data.count) := [(facetIndex 6), (facetIndex 11), (facetIndex 12), (facetIndex 24), (facetIndex 31), (facetIndex 37), (facetIndex 59), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0035_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0035 = true := by
  decide +kernel
theorem leaf0035_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0035 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0035_counts_checked
def leaf0036 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 12), (facetIndex 24), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0036_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0036 = true := by
  decide +kernel
theorem leaf0036_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0036 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0036_counts_checked
def leaf0037 : List (Fin data.count) := [(facetIndex 2), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 30), (facetIndex 50), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0037_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0037 = true := by
  decide +kernel
theorem leaf0037_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0037 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0037_counts_checked
def leaf0038 : List (Fin data.count) := [(facetIndex 4), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 41), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0038_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0038 = true := by
  decide +kernel
theorem leaf0038_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0038 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0038_counts_checked
def leaf0039 : List (Fin data.count) := [(facetIndex 6), (facetIndex 17), (facetIndex 18), (facetIndex 24), (facetIndex 30), (facetIndex 37), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0039_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0039 = true := by
  decide +kernel
theorem leaf0039_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0039 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0039_counts_checked
def leaf0040 : List (Fin data.count) := [(facetIndex 7), (facetIndex 17), (facetIndex 18), (facetIndex 24), (facetIndex 41), (facetIndex 46), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0040_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0040 = true := by
  decide +kernel
theorem leaf0040_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0040 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0040_counts_checked
def leaf0041 : List (Fin data.count) := [(facetIndex 4), (facetIndex 11), (facetIndex 12), (facetIndex 24), (facetIndex 42), (facetIndex 52), (facetIndex 59), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0041_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0041 = true := by
  decide +kernel
theorem leaf0041_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0041 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0041_counts_checked
def leaf0042 : List (Fin data.count) := [(facetIndex 6), (facetIndex 11), (facetIndex 12), (facetIndex 21), (facetIndex 31), (facetIndex 37), (facetIndex 59), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0042_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0042 = true := by
  decide +kernel
theorem leaf0042_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0042 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0042_counts_checked
def leaf0043 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 12), (facetIndex 21), (facetIndex 42), (facetIndex 46), (facetIndex 59), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 81), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0043_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0043 = true := by
  decide +kernel
theorem leaf0043_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0043 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0043_counts_checked
def leaf0044 : List (Fin data.count) := [(facetIndex 2), (facetIndex 17), (facetIndex 18), (facetIndex 24), (facetIndex 30), (facetIndex 50), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 88), (facetIndex 90), (facetIndex 93)]
theorem leaf0044_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0044 = true := by
  decide +kernel
theorem leaf0044_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0044 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0044_counts_checked
def leaf0045 : List (Fin data.count) := [(facetIndex 4), (facetIndex 17), (facetIndex 18), (facetIndex 24), (facetIndex 41), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 82), (facetIndex 90), (facetIndex 94)]
theorem leaf0045_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0045 = true := by
  decide +kernel
theorem leaf0045_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0045 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0045_counts_checked
def leaf0046 : List (Fin data.count) := [(facetIndex 6), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 30), (facetIndex 37), (facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 78), (facetIndex 88), (facetIndex 90), (facetIndex 95)]
theorem leaf0046_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0046 = true := by
  decide +kernel
theorem leaf0046_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0046 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0046_counts_checked
def leaf0047 : List (Fin data.count) := [(facetIndex 7), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 41), (facetIndex 46), (facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 78), (facetIndex 82), (facetIndex 90), (facetIndex 96)]
theorem leaf0047_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0047 = true := by
  decide +kernel
theorem leaf0047_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0047 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0047_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
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
 (.branch 46
 (.leaf (leaf0045))
 (.branch 47
 (.leaf (leaf0046))
 (.leaf (leaf0047))))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":24},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0006\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0020\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0043\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0040\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0046\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0046\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0057\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0057\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0057\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0069\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0069\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0065\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0065\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0065\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0074\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0066\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0066\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0066\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0080\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0077\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0085\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0083\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0078\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record008" 195

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record008" "{\"ridges\":[[2,259],[2,261],[2,262],[3,41],[4,259],[4,265],[4,266],[6,19],[6,529],[6,530],[7,515],[7,546],[8,259],[8,515],[8,769],[9,13],[10,13],[10,265],[11,21],[12,41],[13,81],[13,97],[14,529],[14,545],[15,14],[16,14],[16,266],[17,22],[18,42],[20,50],[20,530],[20,546],[21,76],[22,84],[23,168],[24,224],[25,11],[25,13],[25,14],[25,21],[25,22],[26,41],[26,42],[29,21],[29,50],[30,19],[30,22],[31,7],[31,19],[32,19],[32,261],[34,102],[35,165],[37,515],[37,769],[37,770],[38,11],[38,19],[38,41],[38,42],[39,73],[40,153],[41,35],[42,11],[42,35],[42,41],[43,35],[46,515],[46,769],[47,97],[50,19],[50,259],[50,769],[50,770],[52,546],[52,769],[53,60],[54,21],[54,73],[54,76],[56,69],[57,13],[58,69],[59,69],[59,73],[59,261],[59,265],[59,268],[60,21],[60,97],[61,21],[62,21],[62,148],[62,196],[63,21],[63,261],[63,529],[63,788],[64,165],[65,41],[65,81],[68,41],[68,73],[68,97],[68,168],[68,200],[69,41],[69,265],[69,545],[69,808],[70,81],[70,97],[71,81],[71,97],[71,529],[71,560],[74,138],[75,14],[76,14],[76,134],[77,134],[78,134],[78,138],[78,262],[78,266],[78,268],[79,22],[79,102],[80,22],[80,50],[80,162],[80,176],[81,22],[81,196],[81,208],[82,22],[82,262],[82,530],[82,770],[82,788],[83,134],[85,42],[85,50],[87,42],[87,200],[87,224],[88,42],[88,266],[88,546],[88,770],[88,808],[89,162],[90,162],[90,176],[90,530],[90,546],[90,560],[93,84],[93,148],[94,104],[94,196],[94,224],[95,84],[95,196],[96,112],[96,168],[96,200]],\"owners\":[[31,7,[0,2,26,27,34,37],[1,28,29,30,33,35,36]],[25,11,[3,4,41,42,44,45,46],[0,27,28,38,39,40]],[38,11,[0,4,27,28,45,46],[3,25,39,40,41,42,44]],[42,11,[0,4,25,27,39,46],[3,28,38,40,41,44,45]],[76,14,[0,16,25,27,73],[15,26,72,74,75,77]],[30,19,[5,6,38,40,48,50],[1,25,31,32,39,47,49]],[32,19,[5,6,38,39,40,47,48,49],[1,25,30,31,50]],[30,22,[17,72,74,80,82],[1,25,29,32,33,73,79,81]],[4,259,[2,8,32,50,52],[43]],[8,259,[2,4,32,43],[50,52]],[50,259,[2,4,43],[8,32,52]],[2,261,[10,59,63],[32,37]],[32,261,[10,59],[2,37,63]],[59,261,[2,32,37,63],[10]],[63,261,[2,10,59],[32,37]],[2,262,[16,78,82],[32,37]],[82,262,[2,16,78],[32,37]],[41,35,[5,7,29,35,48,52],[3,26,34,42,43,47,51]],[42,35,[5,7,29,34,47,52],[3,26,35,41,43,48,51]],[43,35,[5,7,29,34,35,47,48,51],[3,26,41,42,52]],[42,41,[12,53,56,65,69],[3,26,38,43,44,57,66,68]],[10,265,[4,43,46,69],[59]],[59,265,[4,43,46,69],[10]],[16,266,[4,43,46,88],[78]],[78,266,[4,43,46,88],[16]],[80,50,[5,20,38,47,84],[19,29,72,79,85,89]],[7,515,[6,8,33,37,46],[44]],[8,515,[6,7,33,44],[37,46]],[37,515,[6,7,44],[8,33,46]],[46,515,[6,7,33],[8,37,44]],[14,529,[6,33,50,63],[71]],[20,530,[6,33,50,82],[90]],[14,545,[7,44,52,69],[71]],[69,545,[7,14,71],[44,52]],[20,546,[7,44,52,88],[90]],[52,546,[20,90],[7,44,88]],[8,769,[63,69],[37,46,50,52]],[37,769,[69],[8,46,50,52,63]],[46,769,[63],[8,37,50,52,69]],[50,769,[69],[8,37,46,52,63]],[52,769,[63],[8,37,46,50,69]],[37,770,[88],[8,46,50,52,82]],[50,770,[88],[8,37,46,52,82]],[82,770,[8,46,52,88],[37,50]],[88,770,[8,37,50,82],[46,52]],[56,69,[11,30,36,62],[9,27,34,58,59,60,64]],[58,69,[11,30,34,60],[9,27,36,56,59,62,64]],[59,69,[11,30,34,36,60,62,64],[9,27,56,58]],[54,73,[12,41,45,68],[9,27,39,58,59,65,67]],[59,73,[12,39,41,45,65,67,68],[9,27,54,58]],[21,76,[9,27,54,56,59,73,75,91],[77,93,94]],[54,76,[21,75,77,94],[9,27,56,59,73,91,93]],[59,268,[16,78],[10]],[78,268,[10,59],[16]],[13,81,[11,30,39,49,54,62,67],[47,65,70,71]],[65,81,[11,30,49,62],[13,39,47,54,67,70,71]],[70,81,[11,30,39,54],[13,47,49,62,65,67,71]],[71,81,[11,30,39,49,54,62,67],[13,47,65,70]],[22,84,[11,30,54,60,73,79,91],[81,93,95]],[93,84,[11,30,60,79],[22,54,73,81,91,95]],[95,84,[11,30,54,73],[22,60,79,81,91,93]],[13,97,[12,34,41,51,56,64,68],[47,60,70,71]],[47,97,[12,56,64,68],[13,34,41,51,60,70,71]],[60,97,[12,41,51,68],[13,34,47,56,64,70,71]],[68,97,[13,34,47,60,71],[12,41,51,56,64,70]],[70,97,[12,34,41,56],[13,47,51,60,64,68,71]],[71,97,[12,34,41,51,56,64,68],[13,47,60,70]],[94,104,[12,41,65,84],[23,56,75,87,91,96]],[96,112,[13,47,60,71,79],[24,65,84,89,91,95]],[71,560,[20,90],[14]],[90,560,[14,71],[20]],[76,134,[17,31,36,81],[15,28,35,77,78,80,83]],[77,134,[17,31,35,80],[15,28,36,76,78,81,83]],[78,134,[17,31,35,36,80,81,83],[15,28,76,77]],[83,134,[15,17,28,31,78],[35,36,76,77,80,81]],[74,138,[18,42,45,87],[15,28,40,77,78,85,86]],[78,138,[18,40,42,45,85,86,87],[15,28,74,77]],[62,148,[17,74,80,92],[22,31,55,61,93,95]],[93,148,[17,31,61,80],[22,55,62,74,92,95]],[80,162,[18,42,51,87],[19,35,48,76,83,89,90]],[89,162,[18,35,42,76],[19,48,51,80,83,87,90]],[90,162,[18,35,42,51,76,83,87],[19,48,80,89]],[23,168,[18,42,57,66,76,85,92],[68,94,96]],[68,168,[18,76,85,92],[23,42,57,66,94,96]],[96,168,[18,42,57,76],[23,66,68,85,92,94]],[80,176,[24,66,70,96],[19,48,61,85,90,92,95]],[90,176,[24,61,66,70,92,95,96],[19,48,80,85]],[62,196,[21,77,83,94],[22,36,58,64,81,95]],[81,196,[21,58,64,94],[22,36,62,77,83,95]],[94,196,[22,36,62,81],[21,58,64,77,83,95]],[95,196,[21,36,58,77],[22,62,64,81,83,94]],[68,200,[21,77,86,93],[23,45,58,67,87,96]],[87,200,[21,58,67,93],[23,45,68,77,86,96]],[96,200,[21,45,58,77],[23,67,68,86,87,93]],[81,208,[24,67,70,96],[22,49,62,86,89,93]],[24,224,[23,51,64,68,83,87,94],[70,89,95]],[87,224,[24,64,70,95],[23,51,68,83,89,94]],[94,224,[24,51,70,89],[23,64,68,83,87,95]],[34,102,[75,79,83],[]],[79,102,[34,75,83],[]],[35,165,[57,61,64],[]],[64,165,[35,57,61],[]],[40,153,[55,66,67],[]],[53,60,[72,91,92],[]],[63,788,[82],[]],[82,788,[63],[]],[69,808,[88],[]],[88,808,[69],[]]],\"edges\":[[21,[15,17,21,22,28,31,35,36,55,57,58,61,62,64,74,76,77,78,80,81,83,92,93,94,95]],[22,[2,10,16,32,37,59,63,78,82]],[28,[4,10,16,43,46,59,69,78,88]],[34,[6,14,20,33,50,63,71,82,90]],[35,[12,13,23,24,34,41,47,51,56,60,64,65,68,70,71,75,79,83,84,87,89,91,94,95,96]],[38,[7,14,20,44,52,69,71,88,90]],[44,[8,37,46,50,52,63,69,82,88]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-24,-2],[-25,-4],[-26,-24],[-27,-24],[-28,-6],[-29,-24],[-29,-26],[-30,-27],[-31,-24],[-31,-29],[-31,-30],[-32,-24],[-32,-28],[-32,-29],[-32,-30],[-33,-24],[-34,-24],[-35,-24],[-36,-4],[-36,-24],[-37,-7],[-38,-28],[-40,-26],[-40,-29],[-41,-27],[-41,-30],[-42,-24],[-42,-25],[-42,-40],[-42,-41],[-43,-37],[-43,-40],[-43,-41],[-45,-4],[-45,-25],[-46,-28],[-46,-29],[-46,-40],[-47,-30],[-47,-41],[-48,-28],[-49,-7],[-49,-28],[-49,-31],[-49,-36],[-49,-43],[-49,-45],[-51,-6],[-51,-7],[-51,-32],[-51,-36],[-51,-37],[-51,-49],[-53,-24],[-53,-29],[-54,-24],[-55,-25],[-55,-40],[-57,-30],[-57,-41],[-58,-1],[-58,-24],[-58,-25],[-58,-26],[-58,-27],[-59,-25],[-59,-28],[-59,-29],[-59,-53],[-59,-55],[-61,-27],[-61,-29],[-61,-30],[-61,-41],[-61,-53],[-61,-57],[-61,-59],[-62,-29],[-62,-31],[-62,-32],[-62,-36],[-62,-49],[-64,-37],[-64,-40],[-64,-53],[-64,-55],[-67,-27],[-67,-30],[-67,-34],[-67,-35],[-67,-39],[-67,-40],[-67,-41],[-67,-44],[-67,-47],[-67,-48],[-67,-50],[-67,-55],[-67,-57],[-67,-60],[-67,-61],[-67,-64],[-67,-65],[-67,-66],[-68,-40],[-68,-42],[-68,-43],[-68,-45],[-68,-51],[-69,-30],[-69,-41],[-69,-61],[-69,-67],[-70,-5],[-70,-28],[-70,-37],[-70,-46],[-70,-47],[-70,-59],[-70,-64],[-70,-69],[-72,-24],[-72,-29],[-73,-24],[-73,-30],[-75,-25],[-75,-28],[-75,-33],[-75,-41],[-76,-29],[-76,-40],[-77,-1],[-77,-24],[-77,-25],[-77,-26],[-77,-27],[-79,-30],[-79,-73],[-79,-75],[-80,-26],[-80,-29],[-80,-30],[-80,-40],[-80,-46],[-80,-73],[-80,-76],[-80,-79],[-81,-30],[-81,-31],[-81,-32],[-84,-18],[-84,-24],[-84,-41],[-84,-53],[-84,-73],[-84,-75],[-86,-26],[-86,-29],[-86,-33],[-86,-35],[-86,-38],[-86,-40],[-86,-41],[-86,-44],[-86,-46],[-86,-48],[-86,-67],[-86,-72],[-86,-74],[-86,-75],[-86,-76],[-86,-78],[-86,-80],[-86,-84],[-87,-41],[-88,-29],[-88,-40],[-88,-80],[-88,-86],[-89,-5],[-89,-28],[-89,-37],[-89,-79],[-90,-24],[-91,-24],[-92,-20],[-92,-24],[-92,-53],[-92,-64],[-92,-73],[-92,-84],[-93,-25],[-93,-28],[-93,-55],[-93,-57],[-93,-59],[-93,-75],[-93,-76],[-93,-79],[-93,-86],[-93,-92],[-94,-25],[-94,-28],[-94,-55],[-94,-59],[-94,-75],[-94,-79],[-94,-93],[-95,-24],[-95,-37],[-95,-38],[-95,-39],[-95,-50],[-95,-53],[-95,-63],[-95,-64],[-95,-66],[-95,-67],[-95,-69],[-95,-73],[-95,-82],[-95,-83],[-95,-84],[-95,-85],[-95,-88],[-95,-91],[-95,-92],[-95,-93],[-95,-94],[-30,1,2,25,26,33,36],[-24,3,4,40,41,43,44,45],[-37,1,4,26,27,44,45],[-41,1,4,24,26,38,45],[-9,-10,-24],[-10,-24,-56],[-75,1,16,24,26,72],[-15,-16,-24],[-16,-24,-74],[-29,5,6,37,39,47,49],[-31,5,6,37,38,39,46,47,48],[-6,-29,-37],[-6,-30,-37],[-29,-37,-49],[-30,-37,-49],[-11,-24,-62],[-11,-28,-62],[-24,-59,-62],[-24,-60,-62],[-24,-61,-62],[-28,-53,-62],[-28,-61,-62],[-29,17,71,73,79,81],[-17,-24,-81],[-24,-78,-81],[-24,-79,-81],[-24,-80,-81],[-4,2,8,31,49,51],[-8,2,4,31,42],[-49,2,4,42],[-2,-4,-8],[-2,10,58,62],[-31,10,58],[-58,2,31,36,62],[-62,2,10,58],[-2,16,77,81],[-81,2,16,77],[-2,-77,-81],[-40,5,7,28,34,47,51],[-41,5,7,28,33,46,51],[-42,5,7,28,33,34,46,47,50],[-41,12,52,55,64,68],[-3,-67,-68],[-12,-25,-68],[-12,-37,-68],[-25,-64,-68],[-25,-67,-68],[-37,-67,-68],[-18,-25,-87],[-25,-84,-87],[-25,-86,-87],[-37,-86,-87],[-10,4,42,45,68],[-58,4,42,45,68],[-4,-10,-68],[-4,-58,-68],[-16,4,42,45,87],[-77,4,42,45,87],[-4,-16,-87],[-4,-77,-87],[-79,5,19,37,46,83],[-19,-28,-84],[-7,6,8,32,36,45],[-8,6,7,32,43],[-36,6,7,43],[-45,6,7,32],[-14,6,32,49,62],[-6,-62,-70],[-19,6,32,49,81],[-6,-81,-89],[-14,7,43,51,68],[-68,7,14,70],[-19,7,43,51,87],[-51,19,89],[-7,-87,-89],[-8,62,68],[-36,68],[-45,62],[-49,68],[-51,62],[-36,87],[-49,87],[-81,8,45,51,87],[-87,8,36,49,81],[-55,11,29,35,61],[-57,11,29,33,59],[-58,11,29,33,35,59,61,63],[-53,12,40,44,67],[-58,12,38,40,44,64,66,67],[-38,-58,-67],[-20,9,26,53,55,58,72,74,90],[-53,20,74,76,93],[-58,16,77],[-77,10,58],[-13,11,29,38,48,53,61,66],[-64,11,29,48,61],[-69,11,29,38,53],[-70,11,29,38,48,53,61,66],[-21,11,29,53,59,72,78,90],[-92,11,29,59,78],[-94,11,29,53,72],[-13,12,33,40,50,55,63,67],[-46,12,55,63,67],[-59,12,40,50,67],[-67,13,33,46,59,70],[-69,12,33,40,55],[-70,12,33,40,50,55,63,67],[-93,12,40,64,83],[-95,13,46,59,70,78],[-70,19,89],[-89,14,70],[-75,17,30,35,80],[-76,17,30,34,79],[-77,17,30,34,35,79,80,82],[-82,15,17,27,30,77],[-73,18,41,44,86],[-77,18,39,41,44,84,85,86],[-61,17,73,79,91],[-92,17,30,60,79],[-79,18,41,50,86],[-88,18,34,41,75],[-89,18,34,41,50,75,82,86],[-22,18,41,56,65,75,84,91],[-67,18,75,84,91],[-95,18,41,56,75],[-79,23,65,69,95],[-89,23,60,65,69,91,94,95],[-61,20,76,82,93],[-80,20,57,63,93],[-93,21,35,61,80],[-94,20,35,57,76],[-67,20,76,85,92],[-86,20,57,66,92],[-95,20,44,57,76],[-80,23,66,69,95],[-23,22,50,63,67,82,86,93],[-86,23,63,69,94],[-93,23,50,69,88],[-33,74,78,82],[-78,33,74,82],[-34,56,60,63],[-63,34,56,60],[-39,54,65,66],[-52,71,90,91],[-62,81],[-81,62],[-68,87],[-87,68],[-1,96],[-2,97],[-4,98],[-6,99],[-7,100],[-8,101],[-10,102],[-11,103],[-12,104],[-14,105],[-16,106],[-20,107],[-23,108],[-97,109],[-109,110],[-96,-109,111],[-98,112],[-112,113],[-113,114],[-110,114],[-111,115],[-101,116],[-100,-101,117],[-117,118],[-99,-116,118],[-103,119],[-102,119],[-119,120],[-118,121],[-118,-120,122],[-121,123],[-122,124],[-114,-122,125],[-115,-121,125],[-105,126],[-126,127],[-104,127],[-104,-126,128],[-106,129],[-129,130],[-130,131],[-127,131],[-128,132],[-107,133],[-108,134],[-134,135],[-133,135],[-135,136],[-131,137],[-131,-136,138],[-132,-136,139],[-123,-139,140],[-124,-138,140],[-125,-137,140],[-140],[-141,31,32,36,49],[-31,141],[-32,141],[-36,141],[-49,141],[-142,26,53,55,57,58],[-143,46,59,64,69,70],[-144,27,73,75,76,77],[-145,47,79,84,88,89],[-146,42,43,45,51],[-147,61,80,92,94],[-148,67,86,93,95],[-86,148],[-149,24,28,29,30],[-150,25,37,40,41],[-151,141,142],[-152,141],[-152,142],[-153,144],[-153,145],[-154,143],[-154,153],[-155,151],[-155,152,154],[-156,152],[-156,154],[-157,146,147],[-158,146],[-158,147],[-159,149,150],[-160,149],[-160,150],[-161,148,160],[-162,148],[-161,159],[-162,160],[-163,157,162],[-163,158,161],[-164,158,162],[-164,161],[-165,162],[-166,155,165],[-166,156,164],[-166,163],[166],[-167,62],[-62,167],[-168,68],[-68,168],[-169,81],[-81,169],[-87,170],[-33,171],[-34,171],[-35,171],[-38,172],[-44,172],[-48,173],[-54,173],[-56,173],[-50,174],[-60,174],[-65,174],[-63,175],[-66,175],[-71,176],[-74,176],[-78,177],[-83,177],[-90,177],[-82,178],[-85,178],[-91,178],[-179,168,169],[-169,179],[-168,179],[-180,169],[-168,-169,180],[-181,167,179],[-179,181],[-182,167,180],[-180,182],[-167,181],[-167,-179,182],[-167,-180,183],[-172,184],[-171,184],[-184,185],[-170,185],[-170,-184,186],[-187,181,185],[-185,187],[-181,187],[-181,-185,188],[-181,-186,189],[-182,188],[-182,-185,189],[-183,189],[-175,190],[-174,190],[-190,191],[-173,191],[-178,192],[-177,192],[-192,193],[-176,193],[-193,194],[-191,194],[-188,-194,195],[-189,195],[-195],[-2,-10,-11,-23,-30,-49,-55,-68,-70,-77,-86,-87,-89,-92],[-2,-10,-12,-20,-30,-49,-53,-68,-70,-77,-86,-87,-89,-94],[-2,-12,-14,-23,-30,-49,-58,-59,-68,-77,-86,-87,-89,-92],[-2,-11,-14,-20,-30,-49,-58,-64,-68,-77,-86,-87,-89,-94],[-2,-11,-12,-20,-30,-49,-58,-68,-70,-77,-86,-87,-89,-94],[-2,-11,-12,-23,-30,-49,-58,-68,-70,-77,-86,-87,-89,-92],[-4,-10,-12,-23,-41,-51,-53,-62,-70,-77,-80,-81,-89,-93],[-6,-11,-14,-20,-30,-36,-58,-64,-68,-77,-86,-87,-89,-94],[-7,-12,-14,-20,-41,-45,-58,-59,-62,-77,-80,-81,-89,-95],[-2,-16,-17,-23,-29,-49,-58,-67,-68,-70,-75,-87,-89,-92],[-4,-16,-18,-23,-40,-51,-58,-61,-62,-70,-73,-81,-89,-93],[-6,-17,-19,-20,-29,-36,-58,-67,-68,-70,-77,-84,-87,-94],[-7,-18,-19,-20,-40,-45,-58,-61,-62,-70,-77,-79,-81,-95],[-4,-10,-11,-20,-41,-51,-55,-62,-70,-77,-80,-81,-89,-95],[-6,-12,-14,-23,-30,-36,-58,-59,-68,-77,-86,-87,-89,-92],[-7,-11,-14,-23,-41,-45,-58,-62,-64,-77,-80,-81,-89,-93],[-2,-16,-18,-20,-29,-49,-58,-67,-68,-70,-73,-87,-89,-94],[-4,-16,-17,-20,-40,-51,-58,-61,-62,-70,-75,-81,-89,-95],[-6,-18,-19,-23,-29,-36,-58,-67,-68,-70,-77,-79,-87,-92],[-7,-17,-19,-23,-40,-45,-58,-61,-62,-70,-77,-81,-84,-93],[-4,-11,-14,-23,-41,-51,-58,-62,-64,-77,-80,-81,-89,-93],[-6,-10,-12,-20,-30,-36,-53,-68,-70,-77,-86,-87,-89,-94],[-7,-10,-11,-20,-41,-45,-55,-62,-70,-77,-80,-81,-89,-95],[-2,-18,-19,-23,-29,-49,-58,-67,-68,-70,-77,-79,-87,-92],[-4,-17,-19,-23,-40,-51,-58,-61,-62,-70,-77,-81,-84,-93],[-6,-16,-18,-20,-29,-36,-58,-67,-68,-70,-73,-87,-89,-94],[-7,-16,-17,-20,-40,-45,-58,-61,-62,-70,-75,-81,-89,-95],[-4,-12,-14,-20,-41,-51,-58,-59,-62,-77,-80,-81,-89,-95],[-6,-10,-11,-23,-30,-36,-55,-68,-70,-77,-86,-87,-89,-92],[-7,-10,-12,-23,-41,-45,-53,-62,-70,-77,-80,-81,-89,-93],[-2,-17,-19,-20,-29,-49,-58,-67,-68,-70,-77,-84,-87,-94],[-4,-18,-19,-20,-40,-51,-58,-61,-62,-70,-77,-79,-81,-95],[-6,-16,-17,-23,-29,-36,-58,-67,-68,-70,-75,-87,-89,-92],[-7,-16,-18,-23,-40,-45,-58,-61,-62,-70,-73,-81,-89,-93],[-4,-11,-12,-20,-41,-51,-58,-62,-70,-77,-80,-81,-89,-95],[-6,-11,-12,-23,-30,-36,-58,-68,-70,-77,-86,-87,-89,-92],[-7,-11,-12,-23,-41,-45,-58,-62,-70,-77,-80,-81,-89,-93],[-2,-17,-18,-20,-29,-49,-58,-67,-68,-70,-77,-87,-89,-94],[-4,-17,-18,-20,-40,-51,-58,-61,-62,-70,-77,-81,-89,-95],[-6,-17,-18,-23,-29,-36,-58,-67,-68,-70,-77,-87,-89,-92],[-7,-17,-18,-23,-40,-45,-58,-61,-62,-70,-77,-81,-89,-93],[-4,-11,-12,-23,-41,-51,-58,-62,-70,-77,-80,-81,-89,-93],[-6,-11,-12,-20,-30,-36,-58,-68,-70,-77,-86,-87,-89,-94],[-7,-11,-12,-20,-41,-45,-58,-62,-70,-77,-80,-81,-89,-95],[-2,-17,-18,-23,-29,-49,-58,-67,-68,-70,-77,-87,-89,-92],[-4,-17,-18,-23,-40,-51,-58,-61,-62,-70,-77,-81,-89,-93],[-6,-17,-18,-20,-29,-36,-58,-67,-68,-70,-77,-87,-89,-94],[-7,-17,-18,-20,-40,-45,-58,-61,-62,-70,-77,-81,-89,-95],[15,17,20,21,27,30,34,35,54,56,57,60,61,63,73,75,76,77,79,80,82,91,92,93,94],[2,10,16,31,36,58,62,77,81],[4,10,16,42,45,58,68,77,87],[6,14,19,32,49,62,70,81,89],[12,13,22,23,33,40,46,50,55,59,63,64,67,69,70,74,78,82,83,86,88,90,93,94,95],[7,14,19,43,51,68,70,87,89],[8,36,45,49,51,62,68,81,87]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":24,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":25,\"b\":2},{\"tag\":\"incompatible\",\"a\":26,\"b\":4},{\"tag\":\"incompatible\",\"a\":27,\"b\":25},{\"tag\":\"incompatible\",\"a\":28,\"b\":25},{\"tag\":\"incompatible\",\"a\":29,\"b\":6},{\"tag\":\"incompatible\",\"a\":30,\"b\":25},{\"tag\":\"incompatible\",\"a\":30,\"b\":27},{\"tag\":\"incompatible\",\"a\":31,\"b\":28},{\"tag\":\"incompatible\",\"a\":32,\"b\":25},{\"tag\":\"incompatible\",\"a\":32,\"b\":30},{\"tag\":\"incompatible\",\"a\":32,\"b\":31},{\"tag\":\"incompatible\",\"a\":33,\"b\":25},{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":33,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":34,\"b\":25},{\"tag\":\"incompatible\",\"a\":35,\"b\":25},{\"tag\":\"incompatible\",\"a\":36,\"b\":25},{\"tag\":\"incompatible\",\"a\":37,\"b\":4},{\"tag\":\"incompatible\",\"a\":37,\"b\":25},{\"tag\":\"incompatible\",\"a\":38,\"b\":7},{\"tag\":\"incompatible\",\"a\":39,\"b\":29},{\"tag\":\"incompatible\",\"a\":41,\"b\":27},{\"tag\":\"incompatible\",\"a\":41,\"b\":30},{\"tag\":\"incompatible\",\"a\":42,\"b\":28},{\"tag\":\"incompatible\",\"a\":42,\"b\":31},{\"tag\":\"incompatible\",\"a\":43,\"b\":25},{\"tag\":\"incompatible\",\"a\":43,\"b\":26},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":44,\"b\":38},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":4},{\"tag\":\"incompatible\",\"a\":46,\"b\":26},{\"tag\":\"incompatible\",\"a\":47,\"b\":29},{\"tag\":\"incompatible\",\"a\":47,\"b\":30},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":31},{\"tag\":\"incompatible\",\"a\":48,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":29},{\"tag\":\"incompatible\",\"a\":50,\"b\":7},{\"tag\":\"incompatible\",\"a\":50,\"b\":29},{\"tag\":\"incompatible\",\"a\":50,\"b\":32},{\"tag\":\"incompatible\",\"a\":50,\"b\":37},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":6},{\"tag\":\"incompatible\",\"a\":52,\"b\":7},{\"tag\":\"incompatible\",\"a\":52,\"b\":33},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":38},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":54,\"b\":25},{\"tag\":\"incompatible\",\"a\":54,\"b\":30},{\"tag\":\"incompatible\",\"a\":55,\"b\":25},{\"tag\":\"incompatible\",\"a\":56,\"b\":26},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":58,\"b\":31},{\"tag\":\"incompatible\",\"a\":58,\"b\":42},{\"tag\":\"incompatible\",\"a\":59,\"b\":0},{\"tag\":\"incompatible\",\"a\":59,\"b\":25},{\"tag\":\"incompatible\",\"a\":59,\"b\":26},{\"tag\":\"incompatible\",\"a\":59,\"b\":27},{\"tag\":\"incompatible\",\"a\":59,\"b\":28},{\"tag\":\"incompatible\",\"a\":60,\"b\":26},{\"tag\":\"incompatible\",\"a\":60,\"b\":29},{\"tag\":\"incompatible\",\"a\":60,\"b\":30},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":28},{\"tag\":\"incompatible\",\"a\":62,\"b\":30},{\"tag\":\"incompatible\",\"a\":62,\"b\":31},{\"tag\":\"incompatible\",\"a\":62,\"b\":42},{\"tag\":\"incompatible\",\"a\":62,\"b\":54},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":30},{\"tag\":\"incompatible\",\"a\":63,\"b\":32},{\"tag\":\"incompatible\",\"a\":63,\"b\":33},{\"tag\":\"incompatible\",\"a\":63,\"b\":37},{\"tag\":\"incompatible\",\"a\":63,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":38},{\"tag\":\"incompatible\",\"a\":65,\"b\":41},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":68,\"b\":28},{\"tag\":\"incompatible\",\"a\":68,\"b\":31},{\"tag\":\"incompatible\",\"a\":68,\"b\":35},{\"tag\":\"incompatible\",\"a\":68,\"b\":36},{\"tag\":\"incompatible\",\"a\":68,\"b\":40},{\"tag\":\"incompatible\",\"a\":68,\"b\":41},{\"tag\":\"incompatible\",\"a\":68,\"b\":42},{\"tag\":\"incompatible\",\"a\":68,\"b\":45},{\"tag\":\"incompatible\",\"a\":68,\"b\":48},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":51},{\"tag\":\"incompatible\",\"a\":68,\"b\":56},{\"tag\":\"incompatible\",\"a\":68,\"b\":58},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":43},{\"tag\":\"incompatible\",\"a\":69,\"b\":44},{\"tag\":\"incompatible\",\"a\":69,\"b\":46},{\"tag\":\"incompatible\",\"a\":69,\"b\":52},{\"tag\":\"incompatible\",\"a\":70,\"b\":31},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":70,\"b\":62},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":5},{\"tag\":\"incompatible\",\"a\":71,\"b\":29},{\"tag\":\"incompatible\",\"a\":71,\"b\":38},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":48},{\"tag\":\"incompatible\",\"a\":71,\"b\":60},{\"tag\":\"incompatible\",\"a\":71,\"b\":65},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":25},{\"tag\":\"incompatible\",\"a\":73,\"b\":30},{\"tag\":\"incompatible\",\"a\":74,\"b\":25},{\"tag\":\"incompatible\",\"a\":74,\"b\":31},{\"tag\":\"incompatible\",\"a\":76,\"b\":26},{\"tag\":\"incompatible\",\"a\":76,\"b\":29},{\"tag\":\"incompatible\",\"a\":76,\"b\":34},{\"tag\":\"incompatible\",\"a\":76,\"b\":42},{\"tag\":\"incompatible\",\"a\":77,\"b\":30},{\"tag\":\"incompatible\",\"a\":77,\"b\":41},{\"tag\":\"incompatible\",\"a\":78,\"b\":0},{\"tag\":\"incompatible\",\"a\":78,\"b\":25},{\"tag\":\"incompatible\",\"a\":78,\"b\":26},{\"tag\":\"incompatible\",\"a\":78,\"b\":27},{\"tag\":\"incompatible\",\"a\":78,\"b\":28},{\"tag\":\"incompatible\",\"a\":80,\"b\":31},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":27},{\"tag\":\"incompatible\",\"a\":81,\"b\":30},{\"tag\":\"incompatible\",\"a\":81,\"b\":31},{\"tag\":\"incompatible\",\"a\":81,\"b\":41},{\"tag\":\"incompatible\",\"a\":81,\"b\":47},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":31},{\"tag\":\"incompatible\",\"a\":82,\"b\":32},{\"tag\":\"incompatible\",\"a\":82,\"b\":33},{\"tag\":\"incompatible\",\"a\":85,\"b\":18},{\"tag\":\"incompatible\",\"a\":85,\"b\":25},{\"tag\":\"incompatible\",\"a\":85,\"b\":42},{\"tag\":\"incompatible\",\"a\":85,\"b\":54},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":85,\"b\":76},{\"tag\":\"incompatible\",\"a\":87,\"b\":27},{\"tag\":\"incompatible\",\"a\":87,\"b\":30},{\"tag\":\"incompatible\",\"a\":87,\"b\":34},{\"tag\":\"incompatible\",\"a\":87,\"b\":36},{\"tag\":\"incompatible\",\"a\":87,\"b\":39},{\"tag\":\"incompatible\",\"a\":87,\"b\":41},{\"tag\":\"incompatible\",\"a\":87,\"b\":42},{\"tag\":\"incompatible\",\"a\":87,\"b\":45},{\"tag\":\"incompatible\",\"a\":87,\"b\":47},{\"tag\":\"incompatible\",\"a\":87,\"b\":49},{\"tag\":\"incompatible\",\"a\":87,\"b\":68},{\"tag\":\"incompatible\",\"a\":87,\"b\":73},{\"tag\":\"incompatible\",\"a\":87,\"b\":75},{\"tag\":\"incompatible\",\"a\":87,\"b\":76},{\"tag\":\"incompatible\",\"a\":87,\"b\":77},{\"tag\":\"incompatible\",\"a\":87,\"b\":79},{\"tag\":\"incompatible\",\"a\":87,\"b\":81},{\"tag\":\"incompatible\",\"a\":87,\"b\":85},{\"tag\":\"incompatible\",\"a\":88,\"b\":42},{\"tag\":\"incompatible\",\"a\":89,\"b\":30},{\"tag\":\"incompatible\",\"a\":89,\"b\":41},{\"tag\":\"incompatible\",\"a\":89,\"b\":81},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":5},{\"tag\":\"incompatible\",\"a\":90,\"b\":29},{\"tag\":\"incompatible\",\"a\":90,\"b\":38},{\"tag\":\"incompatible\",\"a\":90,\"b\":80},{\"tag\":\"incompatible\",\"a\":91,\"b\":25},{\"tag\":\"incompatible\",\"a\":92,\"b\":25},{\"tag\":\"incompatible\",\"a\":93,\"b\":21},{\"tag\":\"incompatible\",\"a\":93,\"b\":25},{\"tag\":\"incompatible\",\"a\":93,\"b\":54},{\"tag\":\"incompatible\",\"a\":93,\"b\":65},{\"tag\":\"incompatible\",\"a\":93,\"b\":74},{\"tag\":\"incompatible\",\"a\":93,\"b\":85},{\"tag\":\"incompatible\",\"a\":94,\"b\":26},{\"tag\":\"incompatible\",\"a\":94,\"b\":29},{\"tag\":\"incompatible\",\"a\":94,\"b\":56},{\"tag\":\"incompatible\",\"a\":94,\"b\":58},{\"tag\":\"incompatible\",\"a\":94,\"b\":60},{\"tag\":\"incompatible\",\"a\":94,\"b\":76},{\"tag\":\"incompatible\",\"a\":94,\"b\":77},{\"tag\":\"incompatible\",\"a\":94,\"b\":80},{\"tag\":\"incompatible\",\"a\":94,\"b\":87},{\"tag\":\"incompatible\",\"a\":94,\"b\":93},{\"tag\":\"incompatible\",\"a\":95,\"b\":26},{\"tag\":\"incompatible\",\"a\":95,\"b\":29},{\"tag\":\"incompatible\",\"a\":95,\"b\":56},{\"tag\":\"incompatible\",\"a\":95,\"b\":60},{\"tag\":\"incompatible\",\"a\":95,\"b\":76},{\"tag\":\"incompatible\",\"a\":95,\"b\":80},{\"tag\":\"incompatible\",\"a\":95,\"b\":94},{\"tag\":\"incompatible\",\"a\":96,\"b\":25},{\"tag\":\"incompatible\",\"a\":96,\"b\":38},{\"tag\":\"incompatible\",\"a\":96,\"b\":39},{\"tag\":\"incompatible\",\"a\":96,\"b\":40},{\"tag\":\"incompatible\",\"a\":96,\"b\":51},{\"tag\":\"incompatible\",\"a\":96,\"b\":54},{\"tag\":\"incompatible\",\"a\":96,\"b\":64},{\"tag\":\"incompatible\",\"a\":96,\"b\":65},{\"tag\":\"incompatible\",\"a\":96,\"b\":67},{\"tag\":\"incompatible\",\"a\":96,\"b\":68},{\"tag\":\"incompatible\",\"a\":96,\"b\":70},{\"tag\":\"incompatible\",\"a\":96,\"b\":74},{\"tag\":\"incompatible\",\"a\":96,\"b\":83},{\"tag\":\"incompatible\",\"a\":96,\"b\":84},{\"tag\":\"incompatible\",\"a\":96,\"b\":85},{\"tag\":\"incompatible\",\"a\":96,\"b\":86},{\"tag\":\"incompatible\",\"a\":96,\"b\":89},{\"tag\":\"incompatible\",\"a\":96,\"b\":92},{\"tag\":\"incompatible\",\"a\":96,\"b\":93},{\"tag\":\"incompatible\",\"a\":96,\"b\":94},{\"tag\":\"incompatible\",\"a\":96,\"b\":95},{\"tag\":\"mate\",\"ridge\":7,\"a\":31,\"owners\":[0,2,26,27,34,37]},{\"tag\":\"mate\",\"ridge\":11,\"a\":25,\"owners\":[3,4,41,42,44,45,46]},{\"tag\":\"mate\",\"ridge\":11,\"a\":38,\"owners\":[0,4,27,28,45,46]},{\"tag\":\"mate\",\"ridge\":11,\"a\":42,\"owners\":[0,4,25,27,39,46]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[9,10,25]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[10,25,57]},{\"tag\":\"mate\",\"ridge\":14,\"a\":76,\"owners\":[0,16,25,27,73]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[15,16,25]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[16,25,75]},{\"tag\":\"mate\",\"ridge\":19,\"a\":30,\"owners\":[5,6,38,40,48,50]},{\"tag\":\"mate\",\"ridge\":19,\"a\":32,\"owners\":[5,6,38,39,40,47,48,49]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[6,30,38]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[6,31,38]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[30,38,50]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[31,38,50]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[11,25,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[11,29,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[25,60,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[25,61,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[25,62,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[29,54,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[29,62,63]},{\"tag\":\"mate\",\"ridge\":22,\"a\":30,\"owners\":[17,72,74,80,82]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[17,25,82]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[25,79,82]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[25,80,82]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[25,81,82]},{\"tag\":\"mate\",\"ridge\":259,\"a\":4,\"owners\":[2,8,32,50,52]},{\"tag\":\"mate\",\"ridge\":259,\"a\":8,\"owners\":[2,4,32,43]},{\"tag\":\"mate\",\"ridge\":259,\"a\":50,\"owners\":[2,4,43]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[2,4,8]},{\"tag\":\"mate\",\"ridge\":261,\"a\":2,\"owners\":[10,59,63]},{\"tag\":\"mate\",\"ridge\":261,\"a\":32,\"owners\":[10,59]},{\"tag\":\"mate\",\"ridge\":261,\"a\":59,\"owners\":[2,32,37,63]},{\"tag\":\"mate\",\"ridge\":261,\"a\":63,\"owners\":[2,10,59]},{\"tag\":\"mate\",\"ridge\":262,\"a\":2,\"owners\":[16,78,82]},{\"tag\":\"mate\",\"ridge\":262,\"a\":82,\"owners\":[2,16,78]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[2,78,82]},{\"tag\":\"mate\",\"ridge\":35,\"a\":41,\"owners\":[5,7,29,35,48,52]},{\"tag\":\"mate\",\"ridge\":35,\"a\":42,\"owners\":[5,7,29,34,47,52]},{\"tag\":\"mate\",\"ridge\":35,\"a\":43,\"owners\":[5,7,29,34,35,47,48,51]},{\"tag\":\"mate\",\"ridge\":41,\"a\":42,\"owners\":[12,53,56,65,69]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[3,68,69]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[12,26,69]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[12,38,69]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[26,65,69]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[26,68,69]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[38,68,69]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[18,26,88]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[26,85,88]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[26,87,88]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[38,87,88]},{\"tag\":\"mate\",\"ridge\":265,\"a\":10,\"owners\":[4,43,46,69]},{\"tag\":\"mate\",\"ridge\":265,\"a\":59,\"owners\":[4,43,46,69]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[4,10,69]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[4,59,69]},{\"tag\":\"mate\",\"ridge\":266,\"a\":16,\"owners\":[4,43,46,88]},{\"tag\":\"mate\",\"ridge\":266,\"a\":78,\"owners\":[4,43,46,88]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[4,16,88]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[4,78,88]},{\"tag\":\"mate\",\"ridge\":50,\"a\":80,\"owners\":[5,20,38,47,84]},{\"tag\":\"three\",\"ridge\":50,\"vertices\":[20,29,85]},{\"tag\":\"mate\",\"ridge\":515,\"a\":7,\"owners\":[6,8,33,37,46]},{\"tag\":\"mate\",\"ridge\":515,\"a\":8,\"owners\":[6,7,33,44]},{\"tag\":\"mate\",\"ridge\":515,\"a\":37,\"owners\":[6,7,44]},{\"tag\":\"mate\",\"ridge\":515,\"a\":46,\"owners\":[6,7,33]},{\"tag\":\"mate\",\"ridge\":529,\"a\":14,\"owners\":[6,33,50,63]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[6,63,71]},{\"tag\":\"mate\",\"ridge\":530,\"a\":20,\"owners\":[6,33,50,82]},{\"tag\":\"three\",\"ridge\":530,\"vertices\":[6,82,90]},{\"tag\":\"mate\",\"ridge\":545,\"a\":14,\"owners\":[7,44,52,69]},{\"tag\":\"mate\",\"ridge\":545,\"a\":69,\"owners\":[7,14,71]},{\"tag\":\"mate\",\"ridge\":546,\"a\":20,\"owners\":[7,44,52,88]},{\"tag\":\"mate\",\"ridge\":546,\"a\":52,\"owners\":[20,90]},{\"tag\":\"three\",\"ridge\":546,\"vertices\":[7,88,90]},{\"tag\":\"mate\",\"ridge\":769,\"a\":8,\"owners\":[63,69]},{\"tag\":\"mate\",\"ridge\":769,\"a\":37,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":769,\"a\":46,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":769,\"a\":50,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":769,\"a\":52,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":770,\"a\":37,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":770,\"a\":50,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":770,\"a\":82,\"owners\":[8,46,52,88]},{\"tag\":\"mate\",\"ridge\":770,\"a\":88,\"owners\":[8,37,50,82]},{\"tag\":\"mate\",\"ridge\":69,\"a\":56,\"owners\":[11,30,36,62]},{\"tag\":\"mate\",\"ridge\":69,\"a\":58,\"owners\":[11,30,34,60]},{\"tag\":\"mate\",\"ridge\":69,\"a\":59,\"owners\":[11,30,34,36,60,62,64]},{\"tag\":\"mate\",\"ridge\":73,\"a\":54,\"owners\":[12,41,45,68]},{\"tag\":\"mate\",\"ridge\":73,\"a\":59,\"owners\":[12,39,41,45,65,67,68]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[39,59,68]},{\"tag\":\"mate\",\"ridge\":76,\"a\":21,\"owners\":[9,27,54,56,59,73,75,91]},{\"tag\":\"mate\",\"ridge\":76,\"a\":54,\"owners\":[21,75,77,94]},{\"tag\":\"mate\",\"ridge\":268,\"a\":59,\"owners\":[16,78]},{\"tag\":\"mate\",\"ridge\":268,\"a\":78,\"owners\":[10,59]},{\"tag\":\"mate\",\"ridge\":81,\"a\":13,\"owners\":[11,30,39,49,54,62,67]},{\"tag\":\"mate\",\"ridge\":81,\"a\":65,\"owners\":[11,30,49,62]},{\"tag\":\"mate\",\"ridge\":81,\"a\":70,\"owners\":[11,30,39,54]},{\"tag\":\"mate\",\"ridge\":81,\"a\":71,\"owners\":[11,30,39,49,54,62,67]},{\"tag\":\"mate\",\"ridge\":84,\"a\":22,\"owners\":[11,30,54,60,73,79,91]},{\"tag\":\"mate\",\"ridge\":84,\"a\":93,\"owners\":[11,30,60,79]},{\"tag\":\"mate\",\"ridge\":84,\"a\":95,\"owners\":[11,30,54,73]},{\"tag\":\"mate\",\"ridge\":97,\"a\":13,\"owners\":[12,34,41,51,56,64,68]},{\"tag\":\"mate\",\"ridge\":97,\"a\":47,\"owners\":[12,56,64,68]},{\"tag\":\"mate\",\"ridge\":97,\"a\":60,\"owners\":[12,41,51,68]},{\"tag\":\"mate\",\"ridge\":97,\"a\":68,\"owners\":[13,34,47,60,71]},{\"tag\":\"mate\",\"ridge\":97,\"a\":70,\"owners\":[12,34,41,56]},{\"tag\":\"mate\",\"ridge\":97,\"a\":71,\"owners\":[12,34,41,51,56,64,68]},{\"tag\":\"mate\",\"ridge\":104,\"a\":94,\"owners\":[12,41,65,84]},{\"tag\":\"mate\",\"ridge\":112,\"a\":96,\"owners\":[13,47,60,71,79]},{\"tag\":\"mate\",\"ridge\":560,\"a\":71,\"owners\":[20,90]},{\"tag\":\"mate\",\"ridge\":560,\"a\":90,\"owners\":[14,71]},{\"tag\":\"mate\",\"ridge\":134,\"a\":76,\"owners\":[17,31,36,81]},{\"tag\":\"mate\",\"ridge\":134,\"a\":77,\"owners\":[17,31,35,80]},{\"tag\":\"mate\",\"ridge\":134,\"a\":78,\"owners\":[17,31,35,36,80,81,83]},{\"tag\":\"mate\",\"ridge\":134,\"a\":83,\"owners\":[15,17,28,31,78]},{\"tag\":\"mate\",\"ridge\":138,\"a\":74,\"owners\":[18,42,45,87]},{\"tag\":\"mate\",\"ridge\":138,\"a\":78,\"owners\":[18,40,42,45,85,86,87]},{\"tag\":\"mate\",\"ridge\":148,\"a\":62,\"owners\":[17,74,80,92]},{\"tag\":\"mate\",\"ridge\":148,\"a\":93,\"owners\":[17,31,61,80]},{\"tag\":\"mate\",\"ridge\":162,\"a\":80,\"owners\":[18,42,51,87]},{\"tag\":\"mate\",\"ridge\":162,\"a\":89,\"owners\":[18,35,42,76]},{\"tag\":\"mate\",\"ridge\":162,\"a\":90,\"owners\":[18,35,42,51,76,83,87]},{\"tag\":\"mate\",\"ridge\":168,\"a\":23,\"owners\":[18,42,57,66,76,85,92]},{\"tag\":\"mate\",\"ridge\":168,\"a\":68,\"owners\":[18,76,85,92]},{\"tag\":\"mate\",\"ridge\":168,\"a\":96,\"owners\":[18,42,57,76]},{\"tag\":\"mate\",\"ridge\":176,\"a\":80,\"owners\":[24,66,70,96]},{\"tag\":\"mate\",\"ridge\":176,\"a\":90,\"owners\":[24,61,66,70,92,95,96]},{\"tag\":\"mate\",\"ridge\":196,\"a\":62,\"owners\":[21,77,83,94]},{\"tag\":\"mate\",\"ridge\":196,\"a\":81,\"owners\":[21,58,64,94]},{\"tag\":\"mate\",\"ridge\":196,\"a\":94,\"owners\":[22,36,62,81]},{\"tag\":\"mate\",\"ridge\":196,\"a\":95,\"owners\":[21,36,58,77]},{\"tag\":\"mate\",\"ridge\":200,\"a\":68,\"owners\":[21,77,86,93]},{\"tag\":\"mate\",\"ridge\":200,\"a\":87,\"owners\":[21,58,67,93]},{\"tag\":\"mate\",\"ridge\":200,\"a\":96,\"owners\":[21,45,58,77]},{\"tag\":\"mate\",\"ridge\":208,\"a\":81,\"owners\":[24,67,70,96]},{\"tag\":\"mate\",\"ridge\":224,\"a\":24,\"owners\":[23,51,64,68,83,87,94]},{\"tag\":\"mate\",\"ridge\":224,\"a\":87,\"owners\":[24,64,70,95]},{\"tag\":\"mate\",\"ridge\":224,\"a\":94,\"owners\":[24,51,70,89]},{\"tag\":\"mate\",\"ridge\":102,\"a\":34,\"owners\":[75,79,83]},{\"tag\":\"mate\",\"ridge\":102,\"a\":79,\"owners\":[34,75,83]},{\"tag\":\"mate\",\"ridge\":165,\"a\":35,\"owners\":[57,61,64]},{\"tag\":\"mate\",\"ridge\":165,\"a\":64,\"owners\":[35,57,61]},{\"tag\":\"mate\",\"ridge\":153,\"a\":40,\"owners\":[55,66,67]},{\"tag\":\"mate\",\"ridge\":60,\"a\":53,\"owners\":[72,91,92]},{\"tag\":\"mate\",\"ridge\":788,\"a\":63,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":788,\"a\":82,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":808,\"a\":69,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":808,\"a\":88,\"owners\":[69]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,96]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-2,97]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-4,98]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-6,99]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-7,100]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-8,101]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-10,102]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-11,103]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-12,104]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-14,105]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-16,106]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-20,107]},{\"tag\":\"group_take\",\"kind\":1,\"index\":24,\"member\":24,\"full_literals\":[-23,108]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped1_0005\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-109,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-96,-109,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-112,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-111,false,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-101,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-100,-101,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-117,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-99,-116,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-119,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0015\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-118,false,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0015\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-118,-120,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-121,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-122,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-114,-122,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-115,-121,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0029\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-105,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-126,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-104,-126,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-106,false,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16,17],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-129,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13,14],\"right\":[15,16,17],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-130,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13,14],\"right\":[15,16,17],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-127,false,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13,14],\"right\":[15,16,17],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0026\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-128,false,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-107,false,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23],\"right\":[24],\"left_name\":\"grouped1_0042\",\"right_name\":\"grouped1_0044\",\"joined_name\":\"grouped1_0043\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-108,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22],\"right\":[23,24],\"left_name\":\"grouped1_0039\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0040\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-134,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22],\"right\":[23,24],\"left_name\":\"grouped1_0039\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0040\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-133,false,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18,19,20],\"right\":[21,22,23,24],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-135,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13,14,15,16,17],\"right\":[18,19,20,21,22,23,24],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-131,false,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13,14,15,16,17],\"right\":[18,19,20,21,22,23,24],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-131,-136,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13,14,15,16,17],\"right\":[18,19,20,21,22,23,24],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0027\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-132,-136,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11],\"right\":[12,13,14,15,16,17,18,19,20,21,22,23,24],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-123,-139,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11],\"right\":[12,13,14,15,16,17,18,19,20,21,22,23,24],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-124,-138,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11],\"right\":[12,13,14,15,16,17,18,19,20,21,22,23,24],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"groupKind1\",\"a\":4,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-125,-137,140],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[32,33,37,50],\"full_literals\":[-141,31,32,36,49]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":32,\"full_literals\":[-31,141]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":33,\"full_literals\":[-32,141]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":37,\"full_literals\":[-36,141]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":50,\"full_literals\":[-49,141]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[27,54,56,58,59],\"full_literals\":[-142,26,53,55,57,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[47,60,65,70,71],\"full_literals\":[-143,46,59,64,69,70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[28,74,76,77,78],\"full_literals\":[-144,27,73,75,76,77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[48,80,85,89,90],\"full_literals\":[-145,47,79,84,88,89]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[43,44,46,52],\"full_literals\":[-146,42,43,45,51]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[62,81,93,95],\"full_literals\":[-147,61,80,92,94]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[68,87,94,96],\"full_literals\":[-148,67,86,93,95]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":87,\"full_literals\":[-86,148]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[25,29,30,31],\"full_literals\":[-149,24,28,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[26,38,41,42],\"full_literals\":[-150,25,37,40,41]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0046\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-151,141,142],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0046\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-152,141,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0046\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-152,false,142],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-153,144,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-153,false,145],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0051\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-154,143,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-154,false,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-155,151,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-155,152,154],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-156,152,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0047\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-156,false,154],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-157,146,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-158,146,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-158,false,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-159,149,150],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-160,149,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0062\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-160,false,150],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-161,148,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-162,148,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-161,false,159],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-162,false,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0057\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-163,157,162],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0057\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-163,158,161],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0057\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-164,158,162],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0057\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-164,false,161],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0057\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-165,false,162],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-166,155,165],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-166,156,164],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-166,false,163],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[63],\"full_literals\":[-167,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-62,167]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[69],\"full_literals\":[-168,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-68,168]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[82],\"full_literals\":[-169,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-81,169]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-87,170]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":34,\"full_literals\":[-33,171]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":35,\"full_literals\":[-34,171]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":36,\"full_literals\":[-35,171]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":39,\"full_literals\":[-38,172]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":45,\"full_literals\":[-44,172]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":49,\"full_literals\":[-48,173]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":55,\"full_literals\":[-54,173]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":57,\"full_literals\":[-56,173]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":51,\"full_literals\":[-50,174]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":61,\"full_literals\":[-60,174]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":66,\"full_literals\":[-65,174]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":64,\"full_literals\":[-63,175]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":67,\"full_literals\":[-66,175]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":72,\"full_literals\":[-71,176]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":75,\"full_literals\":[-74,176]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":79,\"full_literals\":[-78,177]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":84,\"full_literals\":[-83,177]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":91,\"full_literals\":[-90,177]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":83,\"full_literals\":[-82,178]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":86,\"full_literals\":[-85,178]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":92,\"full_literals\":[-91,178]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0069\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-179,168,169],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0069\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-169,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0069\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-168,false,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0069\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-180,false,169],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0069\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-168,-169,180],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0065\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-181,167,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0065\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-179,181],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0065\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-182,167,180],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0065\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-180,182],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0065\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-167,false,181],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0065\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-167,-179,182],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0065\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-167,-180,183],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0074\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-172,184],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0074\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-171,false,184],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-184,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-170,false,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-170,-184,186],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-187,181,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-185,187],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0066\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-181,false,187],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0066\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-181,-185,188],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0066\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-181,-186,189],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0066\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-182,false,188],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0066\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-182,-185,189],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0066\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-183,false,189],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0079\",\"right_name\":\"grouped3_0081\",\"joined_name\":\"grouped3_0080\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-175,190],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0079\",\"right_name\":\"grouped3_0081\",\"joined_name\":\"grouped3_0080\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-174,false,190],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"grouped3_0077\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-190,191],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"grouped3_0077\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-173,false,191],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0084\",\"right_name\":\"grouped3_0086\",\"joined_name\":\"grouped3_0085\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-178,192],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0084\",\"right_name\":\"grouped3_0086\",\"joined_name\":\"grouped3_0085\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-177,false,192],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0082\",\"right_name\":\"grouped3_0085\",\"joined_name\":\"grouped3_0083\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-192,193],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0082\",\"right_name\":\"grouped3_0085\",\"joined_name\":\"grouped3_0083\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-176,false,193],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0077\",\"right_name\":\"grouped3_0083\",\"joined_name\":\"grouped3_0078\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-193,194],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0077\",\"right_name\":\"grouped3_0083\",\"joined_name\":\"grouped3_0078\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-191,false,194],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-188,-194,195],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-189,false,195],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[2,10,11,24,31,50,56,69,71,78,87,88,90,93]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[2,10,12,21,31,50,54,69,71,78,87,88,90,95]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[2,12,14,24,31,50,59,60,69,78,87,88,90,93]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[2,11,14,21,31,50,59,65,69,78,87,88,90,95]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[2,11,12,21,31,50,59,69,71,78,87,88,90,95]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[2,11,12,24,31,50,59,69,71,78,87,88,90,93]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[4,10,12,24,42,52,54,63,71,78,81,82,90,94]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[6,11,14,21,31,37,59,65,69,78,87,88,90,95]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[7,12,14,21,42,46,59,60,63,78,81,82,90,96]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[2,16,17,24,30,50,59,68,69,71,76,88,90,93]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[4,16,18,24,41,52,59,62,63,71,74,82,90,94]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[6,17,20,21,30,37,59,68,69,71,78,85,88,95]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[7,18,20,21,41,46,59,62,63,71,78,80,82,96]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[4,10,11,21,42,52,56,63,71,78,81,82,90,96]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[6,12,14,24,31,37,59,60,69,78,87,88,90,93]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[7,11,14,24,42,46,59,63,65,78,81,82,90,94]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[2,16,18,21,30,50,59,68,69,71,74,88,90,95]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[4,16,17,21,41,52,59,62,63,71,76,82,90,96]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[6,18,20,24,30,37,59,68,69,71,78,80,88,93]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[7,17,20,24,41,46,59,62,63,71,78,82,85,94]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[4,11,14,24,42,52,59,63,65,78,81,82,90,94]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[6,10,12,21,31,37,54,69,71,78,87,88,90,95]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[7,10,11,21,42,46,56,63,71,78,81,82,90,96]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[2,18,20,24,30,50,59,68,69,71,78,80,88,93]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[4,17,20,24,41,52,59,62,63,71,78,82,85,94]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[6,16,18,21,30,37,59,68,69,71,74,88,90,95]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[7,16,17,21,41,46,59,62,63,71,76,82,90,96]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[4,12,14,21,42,52,59,60,63,78,81,82,90,96]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[6,10,11,24,31,37,56,69,71,78,87,88,90,93]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[7,10,12,24,42,46,54,63,71,78,81,82,90,94]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[2,17,20,21,30,50,59,68,69,71,78,85,88,95]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[4,18,20,21,41,52,59,62,63,71,78,80,82,96]},{\"tag\":\"block\",\"leaf\":32,\"vertices\":[6,16,17,24,30,37,59,68,69,71,76,88,90,93]},{\"tag\":\"block\",\"leaf\":33,\"vertices\":[7,16,18,24,41,46,59,62,63,71,74,82,90,94]},{\"tag\":\"block\",\"leaf\":34,\"vertices\":[4,11,12,21,42,52,59,63,71,78,81,82,90,96]},{\"tag\":\"block\",\"leaf\":35,\"vertices\":[6,11,12,24,31,37,59,69,71,78,87,88,90,93]},{\"tag\":\"block\",\"leaf\":36,\"vertices\":[7,11,12,24,42,46,59,63,71,78,81,82,90,94]},{\"tag\":\"block\",\"leaf\":37,\"vertices\":[2,17,18,21,30,50,59,68,69,71,78,88,90,95]},{\"tag\":\"block\",\"leaf\":38,\"vertices\":[4,17,18,21,41,52,59,62,63,71,78,82,90,96]},{\"tag\":\"block\",\"leaf\":39,\"vertices\":[6,17,18,24,30,37,59,68,69,71,78,88,90,93]},{\"tag\":\"block\",\"leaf\":40,\"vertices\":[7,17,18,24,41,46,59,62,63,71,78,82,90,94]},{\"tag\":\"block\",\"leaf\":41,\"vertices\":[4,11,12,24,42,52,59,63,71,78,81,82,90,94]},{\"tag\":\"block\",\"leaf\":42,\"vertices\":[6,11,12,21,31,37,59,69,71,78,87,88,90,95]},{\"tag\":\"block\",\"leaf\":43,\"vertices\":[7,11,12,21,42,46,59,63,71,78,81,82,90,96]},{\"tag\":\"block\",\"leaf\":44,\"vertices\":[2,17,18,24,30,50,59,68,69,71,78,88,90,93]},{\"tag\":\"block\",\"leaf\":45,\"vertices\":[4,17,18,24,41,52,59,62,63,71,78,82,90,94]},{\"tag\":\"block\",\"leaf\":46,\"vertices\":[6,17,18,21,30,37,59,68,69,71,78,88,90,95]},{\"tag\":\"block\",\"leaf\":47,\"vertices\":[7,17,18,21,41,46,59,62,63,71,78,82,90,96]},{\"tag\":\"edge\",\"edge\":21,\"owners\":[15,17,21,22,28,31,35,36,55,57,58,61,62,64,74,76,77,78,80,81,83,92,93,94,95]},{\"tag\":\"edge\",\"edge\":22,\"owners\":[2,10,16,32,37,59,63,78,82]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[4,10,16,43,46,59,69,78,88]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[6,14,20,33,50,63,71,82,90]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[12,13,23,24,34,41,47,51,56,60,64,65,68,70,71,75,79,83,84,87,89,91,94,95,96]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[7,14,20,44,52,69,71,88,90]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[8,37,46,50,52,63,69,82,88]}]}"
  "599 163 0 477 476 0\n600 -189 0 543 542 0\n601 -183 0 600 530 0\n602 187 0 524 525 521 512 515 484 507 479 310 311 376 483 305 307 309 598 0\n603 179 -181 0 507 511 483 478 374 0\n604 185 182 0 602 521 523 484 376 480 603 506 516 482 479 375 0\n605 181 0 512 515 507 508 479 483 481 305 307 309 306 308 377 598 0\n606 -186 0 605 600 527 0\n607 179 0 605 603 0\n608 118 -8 32 43 0 383 399 401 402 400 381 382 293 0\n609 114 -8 31 42 0 396 397 395 392 394 391 380 379 258 0\n610 125 4 141 -150 62 0 606 607 375 482 506 480 106 434 376 436 437 313 258 379 391 609 107 435 608 406 484 522 518 489 175 105 307 410 411 407 398 405 393 404 378 384 261 63 64 65 447 232 0\n611 4 141 -150 62 0 606 607 432 375 482 506 480 376 436 437 313 434 484 522 518 489 175 106 105 307 258 610 431 426 418 417 416 388 265 132 134 135 136 447 232 0\n612 141 -150 62 0 607 375 482 506 480 376 434 436 437 313 611 260 284 285 288 289 593 0\n613 -4 58 62 0 607 375 482 506 480 376 19 284 288 289 261 262 593 0\n614 -37 -148 -185 0 605 543 600 607 529 516 479 375 482 506 480 376 105 526 541 539 537 536 501 83 210 274 277 281 337 444 0\n615 -162 -185 0 605 543 600 607 529 516 479 375 482 506 480 376 175 105 526 541 540 534 492 466 468 464 614 447 126 192 276 278 280 354 444 0\n616 -25 -185 0 605 543 600 607 529 516 479 375 482 506 480 376 175 105 526 541 539 537 535 503 538 499 536 500 368 540 533 531 496 532 494 534 492 370 495 493 502 501 505 57 66 126 192 202 273 275 276 278 279 280 352 350 354 331 332 335 336 365 596 0\n617 -28 89 -84 62 0 375 5 13 43 115 291 296 595 0\n618 49 -19 -77 -17 -29 -84 -67 37 -185 0 605 543 599 600 607 477 37 113 102 529 516 479 375 482 506 480 106 307 309 107 442 460 615 471 475 458 453 68 439 114 191 101 469 459 141 443 526 541 539 537 535 504 130 361 99 98 154 457 450 7 438 14 10 95 449 376 540 533 531 497 532 495 534 491 372 239 433 555 0\n619 18 -67 86 75 37 -185 0 605 543 606 477 600 607 599 113 102 101 99 98 88 87 529 516 479 375 482 506 480 106 307 309 107 442 460 470 467 376 175 105 616 447 462 615 471 475 458 454 451 453 457 450 469 459 484 522 518 489 526 541 540 533 531 496 532 494 534 492 370 493 539 537 535 505 504 503 538 498 353 345 349 351 152 154 191 617 446 7 37 68 130 141 252 438 439 361 440 443 285 339 618 259 574 0\n620 -29 89 -49 -70 -18 -67 95 75 -185 0 605 543 599 600 607 477 339 45 44 151 113 101 99 98 95 87 529 516 479 375 482 506 480 106 307 309 107 442 460 615 471 475 458 454 452 451 457 450 469 459 376 526 541 540 533 532 495 7 55 130 141 176 438 441 263 138 207 355 440 443 567 0\n621 -24 -67 -142 0 99 98 3 54 62 438 0\n622 94 -49 -29 -70 -18 -67 95 75 -185 0 605 543 599 477 600 607 44 45 529 516 479 99 98 55 375 482 506 480 106 307 309 107 442 460 615 471 475 457 450 7 438 263 620 183 141 130 113 101 88 87 458 454 451 469 459 376 526 541 540 533 532 495 494 539 537 535 505 356 443 190 348 440 588 0\n623 -77 -94 -89 -49 -29 -70 -18 -67 -185 0 605 543 477 600 607 606 130 99 529 516 479 375 482 506 480 376 484 522 519 487 360 44 45 98 55 106 307 309 107 442 460 615 471 475 457 450 7 438 263 183 141 88 526 541 540 533 531 496 532 494 534 492 370 539 537 535 503 343 581 0\n624 -49 -29 -70 -18 -67 95 75 -185 0 606 600 607 477 99 98 55 529 516 479 375 482 506 480 106 307 309 107 442 460 615 471 475 457 450 7 438 130 87 458 454 451 376 484 522 519 487 44 45 620 263 622 360 623 322 440 560 0\n625 77 -94 -89 -36 -6 -29 -70 -18 -67 75 -185 0 477 600 607 606 130 99 529 516 479 375 482 506 480 376 484 522 519 487 360 98 55 106 307 309 107 442 460 615 471 475 457 450 7 438 87 458 454 451 322 440 569 0\n626 -94 -89 -36 -6 -29 -70 -18 -67 75 -185 0 605 543 606 600 607 477 183 99 98 55 529 516 479 375 482 506 480 106 307 309 107 442 460 615 471 475 457 450 7 438 141 130 88 376 484 522 519 487 526 541 540 533 531 496 532 494 534 492 370 539 537 535 503 360 625 343 590 0\n627 -89 -6 -29 -70 -18 -67 95 75 -185 0 605 543 599 600 607 477 10 14 529 516 479 375 482 506 480 106 307 309 107 442 460 615 471 475 457 449 624 433 99 98 55 450 7 438 141 130 113 101 88 87 458 454 451 469 459 376 526 541 540 533 532 495 494 539 537 535 505 183 626 356 443 190 348 440 583 0\n628 -70 -18 -67 95 75 37 -185 0 605 543 599 600 607 477 529 516 479 375 482 506 480 106 307 309 107 442 460 615 471 475 457 450 621 151 113 101 99 98 95 88 87 470 467 376 175 105 616 447 462 458 454 452 451 449 469 459 526 541 540 533 531 497 532 495 534 491 372 114 115 446 7 55 130 141 176 438 624 10 14 239 433 627 339 441 138 207 355 440 443 562 0\n629 75 -29 -67 86 0 607 477 37 113 102 68 78 478 375 482 509 513 604 615 506 480 106 307 309 107 442 460 471 475 458 453 439 277 218 619 628 0\n630 49 -75 -29 -67 0 477 605 543 599 607 141 101 78 375 482 506 480 106 307 309 107 442 478 509 513 604 615 469 459 206 443 218 113 526 541 539 537 535 505 95 176 156 460 471 475 458 454 452 139 441 103 100 356 90 88 341 123 6 7 99 98 55 457 450 438 61 236 37 102 68 453 439 114 449 277 376 14 10 91 239 433 576 0\n631 -29 -67 86 0 607 605 543 599 477 218 113 103 102 101 100 99 98 95 90 88 6 7 37 55 68 78 123 141 176 307 309 375 478 482 509 506 513 480 604 106 107 376 526 615 442 541 469 460 539 459 471 537 475 535 457 458 505 450 453 454 438 439 452 61 285 629 139 156 206 236 341 441 356 443 630 259 553 0\n632 -49 -146 -70 -75 -67 0 117 114 128 127 97 95 89 42 46 47 53 270 442 0\n633 -51 49 -141 38 -70 -67 0 117 116 114 96 95 91 48 50 51 240 433 0\n634 68 49 -141 0 607 306 480 506 482 149 150 433 0\n635 -58 -70 -75 29 -67 0 599 477 126 93 92 116 447 127 88 62 319 446 462 467 472 470 475 460 457 449 632 633 634 107 108 442 106 0\n636 -68 -146 43 0 106 108 109 442 0\n637 141 150 28 29 -67 0 477 464 468 473 474 455 88 448 449 621 457 446 475 462 472 467 0\n638 -68 58 150 28 29 -67 0 599 600 607 94 93 92 88 107 108 376 272 636 484 460 521 470 529 467 516 462 479 446 613 231 0\n639 -70 -75 29 -67 0 127 126 93 92 116 447 635 637 638 308 634 0\n640 -68 -75 29 -67 0 599 127 126 93 92 88 107 277 636 447 460 638 470 62 467 446 462 0\n641 -37 68 70 0 377 21 31 52 182 302 300 597 0\n642 -75 29 -67 0 93 92 126 127 639 640 641 308 634 447 637 0\n643 -28 -62 29 -67 0 607 600 479 516 529 520 519 485 518 488 104 101 96 36 67 115 246 250 334 324 0\n644 -25 68 0 377 2 28 35 63 134 286 282 594 0\n645 68 29 -67 0 607 93 92 308 480 634 506 482 375 643 637 644 447 116 641 0\n646 -67 86 0 599 600 607 477 88 92 93 218 631 642 645 107 376 481 276 277 636 484 447 460 521 470 529 615 619 467 514 516 471 628 462 510 479 475 483 457 450 621 446 5 13 43 181 296 298 595 0\n647 -28 70 -68 0 607 600 481 376 484 521 529 514 510 483 516 479 5 13 43 181 296 298 595 0\n648 -24 32 49 -141 0 9 20 433 0\n649 -93 -30 -147 0 142 73 201 208 443 0\n650 -24 49 -141 0 12 648 0\n651 -30 -148 -147 86 0 646 73 142 649 444 227 229 443 0\n652 -24 -141 62 42 0 1 62 650 259 613 0\n653 -28 -68 0 115 647 0\n654 -93 58 53 26 -142 0 194 195 438 0\n655 -95 70 59 46 -143 0 216 219 439 0\n656 -93 80 61 -147 0 201 208 443 0\n657 -68 150 86 0 599 600 477 607 464 468 469 646 106 107 376 636 484 460 459 521 470 471 529 467 465 475 516 462 457 479 449 651 652 653 446 72 141 656 444 227 229 443 0\n658 -95 -149 29 -143 30 0 209 216 219 446 36 67 115 439 0\n659 150 86 0 607 477 646 464 468 473 474 455 657 308 480 634 506 449 448 482 457 456 148 375 475 453 78 472 467 465 462 658 444 193 446 3 54 62 654 0\n660 -62 -24 30 29 0 187 185 184 133 124 122 62 56 54 18 17 16 4 3 1 374 245 247 248 249 264 253 254 255 256 266 328 330 314 315 235 234 342 341 237 238 359 371 320 344 592 0\n661 -24 30 29 -150 0 27 660 612 652 0\n662 62 160 -150 0 607 599 375 478 482 509 506 513 480 604 105 107 376 636 616 175 460 447 470 614 465 0\n663 -37 68 0 116 641 0\n664 -40 70 94 92 59 -147 -143 0 38 84 143 439 443 112 0\n665 -45 -58 -14 -11 -89 -77 -64 -23 -80 -41 -93 -62 0 374 299 80 295 559 0\n666 70 43 -93 -147 -145 -144 -143 -142 -62 95 29 -150 0 600 607 543 601 432 374 483 479 517 510 481 663 208 201 199 198 197 196 516 528 541 540 533 531 497 534 490 644 529 521 484 80 664 447 25 30 40 74 111 153 443 140 144 145 178 364 439 440 441 390 85 325 340 422 654 385 387 423 403 412 425 405 413 419 427 430 409 407 608 665 312 287 564 0\n667 -4 8 -11 -58 -89 -77 -23 -80 -41 -70 -93 -62 0 607 543 601 374 267 483 479 517 510 481 120 516 528 541 539 537 535 505 536 502 538 498 373 194 271 82 79 257 585 0\n668 -58 -89 -77 -23 -80 -41 -70 43 -93 -62 29 0 600 607 543 601 432 374 483 479 517 510 481 120 516 528 541 539 537 535 505 536 502 538 498 373 194 271 386 414 419 390 422 423 425 427 430 409 74 30 297 196 540 533 531 496 529 520 519 487 485 80 316 385 403 405 407 608 667 283 295 580 0\n669 -45 -10 -53 -89 -77 -23 -80 -41 -70 -93 -62 0 607 543 601 374 483 479 517 510 481 120 516 528 541 539 537 535 505 536 502 538 498 373 194 271 297 80 295 573 0\n670 -41 -70 43 -93 -147 -145 -144 -142 -62 95 29 0 601 600 607 543 432 121 120 118 208 201 199 198 197 194 479 516 528 541 540 533 531 497 539 537 535 505 536 502 538 498 373 529 521 484 374 483 517 510 481 80 25 30 74 153 271 443 386 140 145 178 364 414 440 441 390 419 422 423 425 427 430 409 668 654 323 384 404 405 407 608 669 312 287 550 0\n671 -89 -51 -4 -17 -77 -58 -61 41 -70 -93 -62 86 0 600 601 607 543 121 479 516 528 541 540 533 532 493 659 374 483 517 510 481 663 644 447 177 367 197 539 537 535 503 529 520 519 486 351 589 0\n672 -4 -17 -77 -58 -61 41 -70 43 -93 -146 -145 -62 86 0 601 607 543 121 479 516 528 541 540 533 532 493 659 374 483 517 510 481 663 644 447 177 367 29 118 199 34 442 671 303 441 568 0\n673 89 -45 -17 -77 -58 -61 -40 -70 -93 -145 -62 0 607 543 80 297 295 121 479 516 528 541 540 533 532 493 177 367 118 199 374 339 441 563 0\n674 -77 -58 -61 41 -70 43 -93 -146 -145 -62 30 86 0 600 601 607 543 121 479 516 528 541 540 533 532 493 659 374 483 517 510 481 663 644 447 177 367 143 29 297 199 197 539 537 535 503 529 520 519 487 486 80 343 672 283 295 673 351 584 0\n675 -45 -89 -18 -16 -73 -58 -61 -40 -70 -93 -62 0 607 543 121 479 516 528 541 540 533 532 493 177 367 297 374 80 295 577 0\n676 43 -93 -147 -146 -145 -144 -143 -142 -62 30 95 29 86 0 600 607 543 601 374 483 479 517 510 481 663 208 201 199 198 197 516 528 541 540 533 532 493 529 520 518 489 644 659 666 118 121 670 447 23 29 143 177 443 367 71 75 654 674 440 322 155 345 441 675 442 283 554 0\n677 30 28 95 29 86 0 601 477 659 646 661 446 463 468 473 474 455 662 79 80 81 82 374 479 433 483 517 449 448 510 457 456 481 475 453 454 644 472 471 451 452 465 460 461 444 663 676 32 33 447 0\n678 -30 -150 0 607 15 26 148 374 482 478 509 506 513 480 604 105 616 447 21 116 244 242 301 296 0\n679 95 29 86 0 477 659 678 646 677 22 36 41 43 67 115 193 653 444 634 466 449 612 473 246 250 251 474 325 326 456 439 453 0\n680 -28 -62 -95 29 0 600 607 543 221 479 516 528 541 539 538 499 529 520 519 485 369 540 534 490 217 214 211 36 67 115 246 251 338 324 0\n681 7 -14 -77 -58 -89 -12 -59 -41 -80 28 -62 -95 24 0 607 600 61 374 299 180 146 479 516 529 520 518 489 60 363 144 140 519 485 80 211 295 269 233 571 0\n682 -80 70 -62 29 86 0 601 607 600 477 432 80 82 79 81 433 449 659 678 661 679 680 446 463 468 473 474 456 454 452 451 453 455 448 479 516 529 520 518 489 374 483 517 510 481 644 225 223 220 214 213 210 646 140 143 144 146 147 447 655 25 33 40 60 129 70 333 441 363 438 440 386 340 299 389 387 421 412 424 415 425 420 428 429 408 406 608 681 552 292 0\n683 70 -62 29 86 0 601 477 80 82 79 81 433 449 659 678 661 679 680 446 463 468 473 474 456 453 457 475 471 461 374 483 479 517 510 481 644 229 227 210 682 443 74 77 447 664 0\n684 -77 -89 -17 -45 -7 -58 -61 -70 -62 -95 86 0 607 600 601 228 221 659 210 374 483 479 517 510 481 644 74 447 131 357 516 529 520 518 489 224 223 212 346 591 0\n685 79 -45 -7 -58 -61 -70 -145 -144 -62 -95 86 0 601 228 221 659 210 374 483 479 517 510 481 644 74 447 131 357 71 118 226 225 223 220 347 441 684 440 322 570 0\n686 -7 -58 -61 -70 -145 -144 -146 -62 -95 86 0 601 228 221 659 210 374 483 479 517 510 481 644 74 447 131 357 32 29 71 117 114 222 220 213 49 442 685 139 290 349 440 556 0\n687 -79 -4 -51 -58 -61 -70 -144 -62 -95 86 0 601 228 221 659 210 374 483 479 517 510 481 644 74 447 131 357 71 117 114 222 220 213 139 290 349 440 575 0\n688 -77 -89 -17 -4 -51 -58 -61 -70 -62 -95 86 0 607 600 601 228 221 659 210 374 483 479 517 510 481 644 74 447 131 357 516 529 520 518 489 224 223 212 346 582 0\n689 -61 -70 -145 -144 -142 -146 28 -62 -95 86 0 601 607 600 297 118 114 479 516 529 520 519 486 374 483 517 510 481 644 80 228 226 225 223 221 220 214 210 659 71 74 76 447 23 29 58 131 438 357 686 295 268 283 687 347 441 688 440 322 561 0\n690 -58 -4 -51 -77 -89 -41 -11 -80 -70 -62 -95 67 0 607 600 228 215 60 358 143 479 516 529 520 518 489 374 217 216 211 318 578 0\n691 7 -77 -89 -41 -11 -80 -70 -142 28 -62 -95 24 67 0 607 600 132 228 215 60 358 140 297 117 114 479 516 529 520 519 485 374 80 214 211 295 269 233 690 438 323 557 0\n692 58 -45 -7 -77 -89 -41 -11 -80 -70 -142 -62 -95 0 228 215 60 358 140 374 214 438 323 566 0\n693 -62 29 86 0 607 601 600 543 477 679 229 228 227 225 223 220 217 216 215 214 211 210 659 678 661 646 79 80 81 82 374 479 433 483 516 517 449 528 529 510 457 541 520 481 475 540 518 644 534 489 490 680 446 463 468 473 471 474 460 461 455 456 448 454 451 452 683 118 689 443 327 143 146 147 447 441 25 30 33 60 129 358 440 691 49 442 692 318 587 0\n694 29 86 0 607 659 678 661 693 375 662 482 463 506 446 480 653 0\n695 86 0 607 659 694 10 14 24 78 375 478 612 482 509 506 513 480 604 107 376 616 175 447 21 243 241 294 433 0\n696 -26 0 695 157 0\n697 -29 0 695 158 0\n698 -33 0 695 159 0\n699 -35 0 695 160 0\n700 -38 0 695 161 0\n701 -40 0 695 162 0\n702 -41 0 695 163 0\n703 -44 0 695 164 0\n704 -46 0 695 165 0\n705 -48 0 695 166 0\n706 -67 0 695 167 0\n707 -72 0 695 168 0\n708 -74 0 695 169 0\n709 -75 0 695 170 0\n710 -76 0 695 171 0\n711 -78 0 695 172 0\n712 -80 0 695 173 0\n713 -84 0 695 174 0\n714 -88 0 695 179 0\n715 -93 0 695 200 0\n716 148 0 695 445 0\n717 36 -64 -11 -20 -58 -14 62 0 714 713 709 710 477 716 701 702 697 712 599 607 698 696 695 375 482 506 480 107 636 478 509 513 604 615 469 459 616 614 447 460 470 467 462 653 106 471 475 457 449 652 446 73 186 443 458 454 451 125 8 440 132 39 452 137 441 15 11 376 433 230 547 0\n718 -20 -58 53 70 62 0 709 710 714 713 477 607 599 716 701 702 712 707 697 704 695 478 375 482 509 513 604 616 614 447 506 480 107 636 460 470 467 462 653 106 615 471 475 457 449 652 446 39 458 454 452 137 441 340 376 304 451 125 8 440 110 73 453 469 459 186 443 205 330 439 717 294 551 0\n719 -36 -59 -23 -92 -58 -14 62 0 709 710 714 713 477 599 716 702 697 607 700 701 703 605 543 706 695 478 375 482 509 513 604 526 541 540 533 531 497 189 318 506 480 376 616 614 447 107 636 460 470 467 462 653 106 615 471 475 457 449 652 446 39 458 454 452 137 441 304 451 125 8 440 294 558 0\n720 -58 53 70 62 0 605 543 709 714 713 477 607 599 716 702 697 710 699 704 706 703 701 700 698 696 695 478 375 482 509 513 604 616 614 447 506 480 107 636 460 470 467 462 653 106 615 471 475 457 449 652 446 39 458 454 452 137 441 340 451 125 8 440 132 110 59 15 11 526 541 540 533 531 497 496 453 376 718 360 362 366 189 439 318 719 433 230 546 0\n721 -55 70 62 0 477 607 599 716 701 702 697 704 478 375 482 509 513 604 616 614 447 506 480 107 636 460 470 467 462 653 106 615 471 475 457 449 652 446 110 458 453 70 86 439 0\n722 -53 70 62 0 477 607 599 716 701 702 697 704 478 375 482 509 513 604 616 614 447 506 480 107 636 460 470 467 462 653 106 615 471 475 457 449 652 446 110 458 453 69 85 439 0\n723 70 62 0 477 607 599 716 701 702 697 696 478 375 482 509 513 604 616 614 447 506 480 107 636 460 470 467 462 653 106 615 471 475 457 449 652 446 59 450 721 722 720 438 0\n724 36 -11 -55 -10 62 0 714 713 709 710 712 605 543 477 607 599 716 701 702 697 698 696 695 478 375 482 509 513 604 616 614 447 506 480 107 636 460 470 467 462 653 106 615 471 475 457 449 652 446 110 526 541 540 533 531 496 204 366 469 459 73 443 723 458 454 451 125 8 440 132 39 452 137 441 15 11 376 433 230 544 0\n725 53 58 62 0 605 543 714 713 599 716 701 702 709 710 607 477 696 700 705 697 712 695 478 375 482 509 513 604 615 506 480 107 636 460 471 475 458 454 451 616 614 447 470 467 462 653 106 457 449 652 446 125 8 440 323 723 376 39 452 137 441 304 110 73 59 526 541 540 533 531 497 496 450 469 459 438 327 204 443 366 724 294 572 0\n726 -36 58 62 0 714 713 709 703 706 708 710 715 477 716 701 702 697 712 599 607 695 375 482 506 480 107 636 478 509 513 604 615 469 459 616 614 447 460 470 467 462 653 106 471 475 457 449 652 446 73 725 188 443 321 317 458 454 451 125 8 440 323 723 376 39 452 137 441 304 294 565 0\n727 58 62 0 714 713 599 716 702 697 709 607 477 706 703 701 715 710 708 712 698 696 695 723 478 375 482 509 513 604 615 506 480 107 636 460 471 475 458 454 451 616 614 447 470 467 462 653 106 457 449 652 446 125 8 440 132 39 452 137 441 73 15 11 469 459 376 323 725 188 317 321 443 726 433 230 545 0\n728 -94 36 62 0 714 713 700 703 605 543 706 599 716 701 702 697 709 607 477 696 698 710 699 695 478 375 482 509 513 604 616 615 506 480 107 636 460 471 475 458 454 451 614 447 470 467 462 653 106 457 449 652 446 125 8 440 132 230 15 11 433 526 541 540 533 531 497 723 120 727 318 496 73 119 316 39 452 137 441 59 376 360 548 0\n729 36 62 0 714 713 709 710 699 477 607 599 716 702 697 700 701 703 605 543 706 698 696 712 695 478 375 482 509 513 604 526 541 540 533 531 497 723 120 727 318 496 616 614 447 506 480 107 636 460 470 467 462 653 106 615 471 475 457 449 652 446 73 119 316 458 454 451 125 8 440 132 39 452 137 441 110 15 11 469 459 376 433 230 728 443 366 549 0\n730 94 62 0 709 710 698 699 700 703 605 543 706 714 713 477 599 716 701 702 697 607 712 695 375 482 506 480 107 376 478 509 513 604 616 614 447 636 460 470 467 462 653 106 615 471 475 457 449 652 446 39 458 454 452 137 441 304 729 294 526 541 540 533 531 497 723 120 727 318 496 73 119 316 451 125 8 440 110 469 459 443 366 579 0\n731 62 0 607 605 716 543 702 599 477 709 713 714 698 697 706 703 701 700 710 699 695 375 478 482 509 506 513 480 604 106 107 376 636 653 526 615 616 614 460 541 447 470 471 540 467 475 533 462 457 458 531 449 454 496 497 652 451 452 446 8 39 59 73 125 137 440 441 304 723 119 120 727 316 318 729 294 730 360 586 0\n732 -31 0 731 79 0\n733 -32 0 731 80 0\n734 -36 0 731 81 0\n735 -49 0 731 82 0\n736 81 0 731 374 0\n737 167 0 731 479 0\n738 -141 0 735 732 734 733 433 0\n739 -30 0 736 148 0\n740 169 0 736 483 0\n741 -180 0 737 601 517 0\n742 -152 0 738 449 0\n743 -24 0 739 731 697 660 0\n744 -168 0 741 740 510 0\n745 -156 0 742 457 0\n746 -68 0 744 481 0\n747 164 0 745 477 475 0\n748 -25 0 746 644 0\n749 -37 0 746 663 0\n750 161 0 747 472 0\n751 -150 0 749 748 701 702 447 0\n752 159 0 750 467 0\n753 -160 0 751 464 0\n754 149 0 752 751 462 0\n755 -162 0 753 468 0\n756 28 0 754 743 739 697 446 0\n757 158 0 755 747 471 0\n758 -59 0 756 67 0\n759 -94 0 756 203 0\n760 -11 0 756 731 246 0\n761 -61 0 756 731 251 0\n762 147 0 757 461 0\n763 92 0 759 761 712 762 443 0\n764 0 760 763 697 758 711 329 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.l) :=
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
 (.leaf (⟨0, by decide⟩))
 (.branch 8
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨0, by decide⟩))))
 (.branch 10
 (.leaf (⟨0, by decide⟩))
 (.branch 11
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨0, by decide⟩))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (⟨0, by decide⟩))
 (.branch 14
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨1, by decide⟩))))
 (.branch 16
 (.leaf (⟨1, by decide⟩))
 (.branch 17
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨1, by decide⟩)))))
 (.branch 21
 (.branch 19
 (.leaf (⟨1, by decide⟩))
 (.branch 20
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨2, by decide⟩))))
 (.branch 22
 (.leaf (⟨2, by decide⟩))
 (.branch 23
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨2, by decide⟩)))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf (⟨2, by decide⟩))
 (.branch 26
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨2, by decide⟩))))
 (.branch 28
 (.leaf (⟨3, by decide⟩))
 (.branch 29
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨3, by decide⟩)))))
 (.branch 33
 (.branch 31
 (.leaf (⟨3, by decide⟩))
 (.branch 32
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
 (.branch 34
 (.leaf (⟨3, by decide⟩))
 (.branch 35
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨4, by decide⟩))))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf (⟨4, by decide⟩))
 (.branch 38
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨4, by decide⟩))))
 (.branch 40
 (.leaf (⟨4, by decide⟩))
 (.branch 41
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))))
 (.branch 45
 (.branch 43
 (.leaf (⟨5, by decide⟩))
 (.branch 44
 (.leaf (⟨5, by decide⟩))
 (.leaf (⟨5, by decide⟩))))
 (.branch 46
 (.leaf (⟨5, by decide⟩))
 (.branch 47
 (.leaf (⟨5, by decide⟩))
 (.leaf (⟨5, by decide⟩))))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.g)) :=
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
 (.leaf ([⟨1, by decide⟩]))
 (.branch 8
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 10
 (.leaf ([⟨4, by decide⟩]))
 (.branch 11
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ([⟨7, by decide⟩]))
 (.branch 14
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))
 (.branch 16
 (.leaf ([⟨3, by decide⟩]))
 (.branch 17
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩])))))
 (.branch 21
 (.branch 19
 (.leaf ([⟨6, by decide⟩]))
 (.branch 20
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 22
 (.leaf ([⟨2, by decide⟩]))
 (.branch 23
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩])))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ([⟨5, by decide⟩]))
 (.branch 26
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))
 (.branch 28
 (.leaf ([⟨1, by decide⟩]))
 (.branch 29
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))))
 (.branch 33
 (.branch 31
 (.leaf ([⟨4, by decide⟩]))
 (.branch 32
 (.leaf ([⟨5, by decide⟩]))
 (.leaf ([⟨6, by decide⟩]))))
 (.branch 34
 (.leaf ([⟨7, by decide⟩]))
 (.branch 35
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ([⟨3, by decide⟩]))
 (.branch 38
 (.leaf ([⟨4, by decide⟩]))
 (.leaf ([⟨5, by decide⟩]))))
 (.branch 40
 (.leaf ([⟨6, by decide⟩]))
 (.branch 41
 (.leaf ([⟨7, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 45
 (.branch 43
 (.leaf ([⟨2, by decide⟩]))
 (.branch 44
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩]))))
 (.branch 46
 (.leaf ([⟨5, by decide⟩]))
 (.branch 47
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨7, by decide⟩]))))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record017
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f4c707c3cb2a2e87a398d62d876c3a2e1b91e1783e3c729c64b91e66539715354b51d70d1b61d4745d0f72364d532cc73c2e2b4acab1ac9b16c3bc1cc789ca745c970de0f43c4f8b0e23491a198560b81e384d1c262946625194558342d074c328c6344c9314d0b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d36d269a4924936934d24924d249249249a492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 16
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
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)])))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)]))))
 (.branch 22
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.leaf ([(facetIndex 21)])))
 (.branch 23
 (.leaf ([(facetIndex 22)]))
 (.leaf ([(facetIndex 23)])))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.leaf ([(facetIndex 25)])))
 (.branch 27
 (.leaf ([(facetIndex 26)]))
 (.leaf ([(facetIndex 27)]))))
 (.branch 30
 (.branch 29
 (.leaf ([(facetIndex 28)]))
 (.leaf ([(facetIndex 29)])))
 (.branch 31
 (.leaf ([(facetIndex 30)]))
 (.leaf ([(facetIndex 31)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "ffbbcdeb38bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 32
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 59), (facetIndex 61), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 58), (facetIndex 60), (facetIndex 69), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 48), (facetIndex 49), (facetIndex 76)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 33), (facetIndex 57), (facetIndex 74)]))
 (.leaf ([(facetIndex 38), (facetIndex 45), (facetIndex 46), (facetIndex 47)])))
 (.branch 7
 (.leaf ([(facetIndex 40), (facetIndex 63), (facetIndex 80), (facetIndex 81)]))
 (.branch 8
 (.leaf ([(facetIndex 55), (facetIndex 71), (facetIndex 72), (facetIndex 78), (facetIndex 85)]))
 (.leaf ([(facetIndex 32), (facetIndex 56), (facetIndex 73), (facetIndex 75)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "700066070284877110000060010148703333225553330605333248z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 54)]))
 (.branch 2
 (.leaf ([(facetIndex 64), (facetIndex 77)]))
 (.leaf ([(facetIndex 84)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 87)]))
 (.leaf ([(facetIndex 62), (facetIndex 67), (facetIndex 68)])))
 (.branch 6
 (.leaf ([(facetIndex 79), (facetIndex 82), (facetIndex 83)]))
 (.leaf ([(facetIndex 86), (facetIndex 88)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6782b40a080000048011z2f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1]
def grouped1_0002 : List Nat := [0, 1, 2, 3]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0004 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def grouped1_0006 : List Nat := [1]
def grouped1_0007 : List Nat := [2]
def grouped1_0008 : List Nat := [2, 3]
def grouped1_0009 : List Nat := [3]
def grouped1_0010 : List Nat := [4]
def grouped1_0011 : List Nat := [4, 5]
def grouped1_0012 : List Nat := [4, 5, 6, 7]
def grouped1_0013 : List Nat := [5]
def grouped1_0014 : List Nat := [6]
def grouped1_0015 : List Nat := [6, 7]
def grouped1_0016 : List Nat := [7]
def grouped1_0017 : List Nat := [8]
def grouped1_0018 : List Nat := [8, 9]
def grouped1_0019 : List Nat := [8, 9, 10, 11]
def grouped1_0020 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]
def grouped1_0021 : List Nat := [9]
def grouped1_0022 : List Nat := [10]
def grouped1_0023 : List Nat := [10, 11]
def grouped1_0024 : List Nat := [11]
def grouped1_0025 : List Nat := [12]
def grouped1_0026 : List Nat := [12, 13]
def grouped1_0027 : List Nat := [12, 13, 14, 15]
def grouped1_0028 : List Nat := [13]
def grouped1_0029 : List Nat := [14, 15]
def grouped1_0030 : List Nat := [16]
def grouped1_0031 : List Nat := [16, 17]
def grouped1_0032 : List Nat := [16, 17, 18, 19]
def grouped1_0033 : List Nat := [16, 17, 18, 19, 20, 21, 22, 23]
def grouped1_0034 : List Nat := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def grouped1_0035 : List Nat := [17]
def grouped1_0036 : List Nat := [18]
def grouped1_0037 : List Nat := [18, 19]
def grouped1_0038 : List Nat := [19]
def grouped1_0039 : List Nat := [20, 21]
def grouped1_0040 : List Nat := [20, 21, 22, 23]
def grouped1_0041 : List Nat := [22]
def grouped1_0042 : List Nat := [22, 23]
def grouped1_0043 : List Nat := [23]
def grouped1_0044 : List Nat := [24]
def grouped1_0045 : List Nat := [24, 25]
def grouped1_0046 : List Nat := [24, 25, 26, 27]
def grouped1_0047 : List Nat := [24, 25, 26, 27, 28, 29, 30, 31]
def grouped1_0048 : List Nat := [25]
def grouped1_0049 : List Nat := [26]
def grouped1_0050 : List Nat := [26, 27]
def grouped1_0051 : List Nat := [27]
def grouped1_0052 : List Nat := [28]
def grouped1_0053 : List Nat := [28, 29]
def grouped1_0054 : List Nat := [28, 29, 30, 31]
def grouped1_0055 : List Nat := [29]
def grouped1_0056 : List Nat := [30, 31]
def grouped2_0057 : List Nat := [0]
def grouped2_0058 : List Nat := [0, 1]
def grouped2_0059 : List Nat := [0, 1, 2, 3]
def grouped2_0061 : List Nat := [1]
def grouped2_0062 : List Nat := [2]
def grouped2_0063 : List Nat := [2, 3]
def grouped2_0064 : List Nat := [3]
def grouped2_0065 : List Nat := [4]
def grouped2_0066 : List Nat := [4, 5]
def grouped2_0067 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0068 : List Nat := [5]
def grouped2_0069 : List Nat := [6]
def grouped2_0070 : List Nat := [6, 7, 8]
def grouped2_0071 : List Nat := [7]
def grouped2_0072 : List Nat := [7, 8]
def grouped2_0073 : List Nat := [8]
def grouped3_0074 : List Nat := [0]
def grouped3_0075 : List Nat := [0, 1, 2]
def grouped3_0077 : List Nat := [1]
def grouped3_0078 : List Nat := [1, 2]
def grouped3_0079 : List Nat := [2]
def grouped3_0080 : List Nat := [3]
def grouped3_0081 : List Nat := [3, 4]
def grouped3_0082 : List Nat := [3, 4, 5, 6]
def grouped3_0083 : List Nat := [4]
def grouped3_0084 : List Nat := [5]
def grouped3_0085 : List Nat := [5, 6]
def grouped3_0086 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_matrix_checked

def leafCount : Nat := 2
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 6), (facetIndex 16), (facetIndex 28), (facetIndex 29), (facetIndex 46), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 71), (facetIndex 73), (facetIndex 76), (facetIndex 81), (facetIndex 87)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 6), (facetIndex 23), (facetIndex 27), (facetIndex 28), (facetIndex 46), (facetIndex 53), (facetIndex 63), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 73), (facetIndex 76), (facetIndex 85), (facetIndex 87)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record017" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":1},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":3},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group\",\"kind\":1,\"index\":23},{\"tag\":\"group\",\"kind\":1,\"index\":24},{\"tag\":\"group\",\"kind\":1,\"index\":27},{\"tag\":\"group\",\"kind\":1,\"index\":28},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0008\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0020\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0042\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0040\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0045\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0050\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0046\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0053\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0054\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0047\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0047\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0063\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0066\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0066\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0072\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0070\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0067\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0067\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0078\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0078\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0081\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0081\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0085\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0082\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0082\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record017" 176

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record017" "{\"ridges\":[[6,11],[6,265],[6,266],[9,259],[13,21],[19,265],[21,769],[27,70],[27,98],[28,266],[29,82],[32,11],[32,13],[32,69],[32,70],[36,7],[40,7],[40,193],[41,774],[42,35],[43,11],[43,67],[44,25],[45,67],[45,98],[46,11],[46,131],[49,769],[49,776],[51,145],[52,82],[52,259],[53,259],[53,274],[54,802],[60,769],[60,776],[61,97],[63,21],[63,69],[63,193],[64,21],[64,788],[65,100],[65,193],[66,69],[66,100],[69,769],[69,776],[70,265],[70,769],[70,776],[71,97],[71,208],[73,70],[73,82],[73,84],[76,42],[76,548],[78,22],[80,70],[81,162],[81,194],[83,184],[84,802],[85,98],[85,208],[85,224],[87,788]],\"owners\":[[36,7,[0,2,3,33,34,39,41],[1,37,38,40]],[40,7,[0,1,2,33,34,37,39,41],[3,36,38]],[46,11,[0,4,6,32,34,43,49],[5,44,45,48]],[32,13,[13,14,15,57,60],[0,33,56,59]],[78,22,[1,24,36,37,74],[26,35,72,79,80]],[42,35,[2,10,11,39,54],[5,35,47,48,50,51]],[43,67,[3,10,12],[7,32,45,52]],[45,67,[3,7,12,52],[10,32,43]],[63,69,[3,17,32,59,66],[16,40,56,65]],[66,69,[3,16,32,40,56,63],[17,59,65]],[73,70,[3,27,40,81],[26,32,75,80]],[44,25,[13,19,55,56,58,67,69],[4,42,43,68]],[76,42,[5,42,45,46,47,82,83],[25,48,72,75,84]],[9,259,[6,33,41,47,49,54],[37,52,53]],[52,259,[6,33,41,47,49,54],[9,37,53]],[53,259,[6,33,41,47,49,54],[9,37,52]],[6,266,[28,74,77,84],[33,47,49]],[28,266,[6,33,47,49,77,84],[74]],[46,131,[8,12,36,40,53],[11,38,44]],[51,145,[22,63],[8,36,44,53,62,68,71]],[53,274,[28,74],[9,37,52]],[61,97,[10,23,45],[17,50,59,66,67,71]],[71,97,[10,17,45,59,66],[23,50,61,67]],[81,162,[11,46,51,83],[30,38,79,85]],[40,193,[22,23],[12,63,65]],[63,193,[12,23],[22,40,65]],[65,193,[12,22],[23,40,63]],[81,194,[12,29],[30,40,80]],[73,84,[16,61,63,88],[26,56,78,80,86]],[65,100,[27,75,78,86],[17,59,61,66,81,88]],[66,100,[27,75,78,81,86,88],[17,59,61,65]],[76,548,[18,66],[31,39]],[21,769,[41,54,64],[49,60,69,70]],[49,769,[64],[21,41,54,60,69,70]],[60,769,[54],[21,41,49,64,69,70]],[69,769,[41,54],[21,49,60,64,70]],[70,769,[41,64],[21,49,54,60,69]],[49,776,[87],[21,60,69,70,77,84]],[60,776,[84],[21,49,69,70,77,87]],[69,776,[77,84],[21,49,60,70,87]],[70,776,[77,87],[21,49,60,69,84]],[71,208,[29,80],[22,63,85,88]],[85,208,[22,63],[29,71,80,88]],[85,224,[23,65],[30,71,81,88]],[41,774,[77],[]],[54,802,[84],[]],[84,802,[54],[]],[64,788,[87],[]],[87,788,[64],[]],[83,184,[68],[]]],\"edges\":[[15,[6,9,28,33,37,41,47,49,52,53,54,74,77,84]],[44,[21,41,49,54,60,64,69,70,77,84,87]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record017" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record017\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-38,-7],[-42,-40],[-47,-42],[-50,-34],[-50,-41],[-50,-42],[-58,-32],[-58,-39],[-58,-46],[-58,-48],[-59,-52],[-61,-31],[-61,-34],[-61,-57],[-61,-60],[-65,-16],[-65,-30],[-65,-43],[-65,-44],[-65,-45],[-66,-13],[-66,-36],[-66,-57],[-66,-58],[-68,-32],[-68,-41],[-71,-15],[-71,-35],[-71,-51],[-71,-55],[-71,-67],[-71,-70],[-72,-29],[-72,-30],[-72,-44],[-72,-53],[-72,-69],[-72,-71],[-73,-28],[-73,-68],[-74,-68],[-75,-32],[-75,-41],[-75,-46],[-75,-58],[-75,-73],[-78,-30],[-78,-43],[-78,-44],[-78,-71],[-79,-36],[-79,-47],[-79,-74],[-79,-75],[-81,-29],[-81,-33],[-81,-37],[-81,-53],[-81,-54],[-81,-56],[-81,-64],[-81,-69],[-81,-72],[-32,1,3,4,29,30,35,37],[-36,1,2,3,29,30,33,35,37],[-42,1,5,7,28,30,39,45],[-7,-28,-42],[-7,-39,-42],[-28,14,15,16,53,56],[-14,-58,-59],[-73,2,24,32,33,69],[-38,3,11,12,35,50],[-39,4,11,13],[-41,4,8,13,48],[-58,4,18,28,55,61],[-61,4,17,28,36,52,58],[-28,-58,-61],[-68,4,25,36,75],[-25,-28,-74],[-40,14,20,51,52,54,62,64],[-71,6,38,41,42,43,76,77],[-10,7,29,37,43,45,50],[-48,7,29,37,43,45,50],[-49,7,29,37,43,45,50],[-7,-20,-65],[-7,26,69,72,78],[-26,7,29,43,45,72,78],[-27,-48,-68],[-42,9,13,32,36,49],[-47,22,58],[-49,26,69],[-57,11,23,41],[-66,11,18,41,55,61],[-25,-41,-79],[-75,12,42,47,77],[-36,22,23],[-58,13,23],[-60,13,22],[-75,13,27],[-68,17,57,58,82],[-60,25,70,73,80],[-61,25,70,73,75,80,82],[-71,19,61],[-21,37,50,59],[-45,59],[-56,50],[-64,37,50],[-65,37,59],[-45,81],[-56,78],[-64,72,78],[-65,72,81],[-66,27,74],[-79,22,58],[-79,23,60],[-37,72],[-50,78],[-78,50],[-59,81],[-81,59],[-77,63],[-1,83],[-2,84],[-3,85],[-4,86],[-5,87],[-6,88],[-7,89],[-8,90],[-9,91],[-11,92],[-12,93],[-13,94],[-14,95],[-18,96],[-19,97],[-22,98],[-23,99],[-24,100],[-25,101],[-26,102],[-84,103],[-83,103],[-86,104],[-85,104],[-104,105],[-103,105],[-88,106],[-87,106],[-90,107],[-89,107],[-107,108],[-106,108],[-106,-107,109],[-108,110],[-109,111],[-105,110],[-105,-108,111],[-91,112],[-93,113],[-92,113],[-113,114],[-112,114],[-95,115],[-94,115],[-115,116],[-116,117],[-114,117],[-117,118],[-110,118],[-110,-117,119],[-111,119],[-111,-117,120],[-96,121],[-97,122],[-122,123],[-121,-122,124],[-99,125],[-98,125],[-125,126],[-123,127],[-123,-126,128],[-124,-126,129],[-100,130],[-101,131],[-131,132],[-130,132],[-102,133],[-133,134],[-134,135],[-132,-134,136],[-127,-135,137],[-127,-136,138],[-128,-135,138],[-129,-135,139],[-118,-139,140],[-119,-138,140],[-120,-137,140],[-140],[-141,35,55,57,60,61],[-142,54,56,64,65],[-143,30,44,45,71],[-144,31,32,33,38,39,40,46,47,48,49],[-145,29,53,69],[-146,34,41,42,43],[-147,36,58,74,75],[-148,51,66,67,73,79],[-149,28,52,68,70],[-150,141],[-150,142],[-151,143],[-151,144],[-152,150],[-152,151],[-153,145,146],[-154,145],[-154,146],[-155,148],[-155,149],[-156,147],[-156,155],[-157,153],[-157,154,156],[-158,154],[-159,152,158],[-159,157],[159],[-37,160],[-50,160],[-59,161],[-72,161],[-78,162],[-81,163],[-62,164],[-63,164],[-76,165],[-80,166],[-82,166],[-162,167],[-161,167],[-161,-162,168],[-167,169],[-168,170],[-160,169],[-160,-167,170],[-163,171],[-163,-164,172],[-166,173],[-165,173],[-171,174],[-171,-173,175],[-172,175],[-169,-175,176],[-170,-174,176],[-176],[-7,-17,-26,-27,-42,-49,-59,-61,-65,-66,-68,-71,-75,-81],[-7,-23,-25,-26,-42,-49,-58,-59,-61,-65,-68,-71,-79,-81],[7,10,26,29,33,37,43,45,48,49,50,69,72,78],[21,37,45,50,56,59,64,65,72,78,81]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":1,\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":3,\"kind\":1},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group\",\"index\":23,\"kind\":1},{\"tag\":\"group\",\"index\":24,\"kind\":1},{\"tag\":\"group\",\"index\":27,\"kind\":1},{\"tag\":\"group\",\"index\":28,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":42,\"b\":6},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":38},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":63,\"b\":36},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":50},{\"tag\":\"incompatible\",\"a\":63,\"b\":52},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":35},{\"tag\":\"incompatible\",\"a\":66,\"b\":38},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":15},{\"tag\":\"incompatible\",\"a\":70,\"b\":34},{\"tag\":\"incompatible\",\"a\":70,\"b\":47},{\"tag\":\"incompatible\",\"a\":70,\"b\":48},{\"tag\":\"incompatible\",\"a\":70,\"b\":49},{\"tag\":\"incompatible\",\"a\":71,\"b\":12},{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":61},{\"tag\":\"incompatible\",\"a\":71,\"b\":63},{\"tag\":\"incompatible\",\"a\":73,\"b\":36},{\"tag\":\"incompatible\",\"a\":73,\"b\":45},{\"tag\":\"incompatible\",\"a\":76,\"b\":14},{\"tag\":\"incompatible\",\"a\":76,\"b\":39},{\"tag\":\"incompatible\",\"a\":76,\"b\":55},{\"tag\":\"incompatible\",\"a\":76,\"b\":59},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":33},{\"tag\":\"incompatible\",\"a\":77,\"b\":34},{\"tag\":\"incompatible\",\"a\":77,\"b\":48},{\"tag\":\"incompatible\",\"a\":77,\"b\":57},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":32},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":73},{\"tag\":\"incompatible\",\"a\":81,\"b\":36},{\"tag\":\"incompatible\",\"a\":81,\"b\":45},{\"tag\":\"incompatible\",\"a\":81,\"b\":50},{\"tag\":\"incompatible\",\"a\":81,\"b\":63},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":34},{\"tag\":\"incompatible\",\"a\":84,\"b\":47},{\"tag\":\"incompatible\",\"a\":84,\"b\":48},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":51},{\"tag\":\"incompatible\",\"a\":85,\"b\":80},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":87,\"b\":33},{\"tag\":\"incompatible\",\"a\":87,\"b\":37},{\"tag\":\"incompatible\",\"a\":87,\"b\":41},{\"tag\":\"incompatible\",\"a\":87,\"b\":57},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"incompatible\",\"a\":87,\"b\":60},{\"tag\":\"incompatible\",\"a\":87,\"b\":69},{\"tag\":\"incompatible\",\"a\":87,\"b\":74},{\"tag\":\"incompatible\",\"a\":87,\"b\":77},{\"tag\":\"mate\",\"ridge\":7,\"a\":36,\"owners\":[0,2,3,33,34,39,41]},{\"tag\":\"mate\",\"ridge\":7,\"a\":40,\"owners\":[0,1,2,33,34,37,39,41]},{\"tag\":\"mate\",\"ridge\":11,\"a\":46,\"owners\":[0,4,6,32,34,43,49]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[6,32,46]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[6,43,46]},{\"tag\":\"mate\",\"ridge\":13,\"a\":32,\"owners\":[13,14,15,57,60]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[13,63,64]},{\"tag\":\"mate\",\"ridge\":22,\"a\":78,\"owners\":[1,24,36,37,74]},{\"tag\":\"mate\",\"ridge\":35,\"a\":42,\"owners\":[2,10,11,39,54]},{\"tag\":\"mate\",\"ridge\":67,\"a\":43,\"owners\":[3,10,12]},{\"tag\":\"mate\",\"ridge\":67,\"a\":45,\"owners\":[3,7,12,52]},{\"tag\":\"mate\",\"ridge\":69,\"a\":63,\"owners\":[3,17,32,59,66]},{\"tag\":\"mate\",\"ridge\":69,\"a\":66,\"owners\":[3,16,32,40,56,63]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[32,63,66]},{\"tag\":\"mate\",\"ridge\":70,\"a\":73,\"owners\":[3,27,40,81]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[27,32,80]},{\"tag\":\"mate\",\"ridge\":25,\"a\":44,\"owners\":[13,19,55,56,58,67,69]},{\"tag\":\"mate\",\"ridge\":42,\"a\":76,\"owners\":[5,42,45,46,47,82,83]},{\"tag\":\"mate\",\"ridge\":259,\"a\":9,\"owners\":[6,33,41,47,49,54]},{\"tag\":\"mate\",\"ridge\":259,\"a\":52,\"owners\":[6,33,41,47,49,54]},{\"tag\":\"mate\",\"ridge\":259,\"a\":53,\"owners\":[6,33,41,47,49,54]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[6,19,70]},{\"tag\":\"mate\",\"ridge\":266,\"a\":6,\"owners\":[28,74,77,84]},{\"tag\":\"mate\",\"ridge\":266,\"a\":28,\"owners\":[6,33,47,49,77,84]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[29,52,73]},{\"tag\":\"mate\",\"ridge\":131,\"a\":46,\"owners\":[8,12,36,40,53]},{\"tag\":\"mate\",\"ridge\":145,\"a\":51,\"owners\":[22,63]},{\"tag\":\"mate\",\"ridge\":274,\"a\":53,\"owners\":[28,74]},{\"tag\":\"mate\",\"ridge\":97,\"a\":61,\"owners\":[10,23,45]},{\"tag\":\"mate\",\"ridge\":97,\"a\":71,\"owners\":[10,17,45,59,66]},{\"tag\":\"three\",\"ridge\":98,\"vertices\":[27,45,85]},{\"tag\":\"mate\",\"ridge\":162,\"a\":81,\"owners\":[11,46,51,83]},{\"tag\":\"mate\",\"ridge\":193,\"a\":40,\"owners\":[22,23]},{\"tag\":\"mate\",\"ridge\":193,\"a\":63,\"owners\":[12,23]},{\"tag\":\"mate\",\"ridge\":193,\"a\":65,\"owners\":[12,22]},{\"tag\":\"mate\",\"ridge\":194,\"a\":81,\"owners\":[12,29]},{\"tag\":\"mate\",\"ridge\":84,\"a\":73,\"owners\":[16,61,63,88]},{\"tag\":\"mate\",\"ridge\":100,\"a\":65,\"owners\":[27,75,78,86]},{\"tag\":\"mate\",\"ridge\":100,\"a\":66,\"owners\":[27,75,78,81,86,88]},{\"tag\":\"mate\",\"ridge\":548,\"a\":76,\"owners\":[18,66]},{\"tag\":\"mate\",\"ridge\":769,\"a\":21,\"owners\":[41,54,64]},{\"tag\":\"mate\",\"ridge\":769,\"a\":49,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":769,\"a\":60,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":769,\"a\":69,\"owners\":[41,54]},{\"tag\":\"mate\",\"ridge\":769,\"a\":70,\"owners\":[41,64]},{\"tag\":\"mate\",\"ridge\":776,\"a\":49,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":776,\"a\":60,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":776,\"a\":69,\"owners\":[77,84]},{\"tag\":\"mate\",\"ridge\":776,\"a\":70,\"owners\":[77,87]},{\"tag\":\"mate\",\"ridge\":208,\"a\":71,\"owners\":[29,80]},{\"tag\":\"mate\",\"ridge\":208,\"a\":85,\"owners\":[22,63]},{\"tag\":\"mate\",\"ridge\":224,\"a\":85,\"owners\":[23,65]},{\"tag\":\"mate\",\"ridge\":774,\"a\":41,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":802,\"a\":54,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":802,\"a\":84,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":788,\"a\":64,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":788,\"a\":87,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":184,\"a\":83,\"owners\":[68]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,83]},{\"tag\":\"group_take\",\"kind\":1,\"index\":1,\"member\":1,\"full_literals\":[-2,84]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-3,85]},{\"tag\":\"group_take\",\"kind\":1,\"index\":3,\"member\":3,\"full_literals\":[-4,86]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-5,87]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-6,88]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-7,89]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-8,90]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-9,91]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-11,92]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-12,93]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-13,94]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-14,95]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-18,96]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-19,97]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-22,98]},{\"tag\":\"group_take\",\"kind\":1,\"index\":23,\"member\":23,\"full_literals\":[-23,99]},{\"tag\":\"group_take\",\"kind\":1,\"index\":24,\"member\":24,\"full_literals\":[-24,100]},{\"tag\":\"group_take\",\"kind\":1,\"index\":27,\"member\":27,\"full_literals\":[-25,101]},{\"tag\":\"group_take\",\"kind\":1,\"index\":28,\"member\":28,\"full_literals\":[-26,102]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-104,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-103,false,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-88,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-89,false,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-107,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-106,false,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-106,-107,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-108,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-109,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-105,-108,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-93,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-112,false,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-95,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-94,false,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-115,false,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-116,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-114,false,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-117,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-117,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0004\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-111,false,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0004\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-111,-117,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0031\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-96,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-97,false,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-122,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-121,-122,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22],\"right\":[23],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0042\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-99,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22],\"right\":[23],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0042\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21],\"right\":[22,23],\"left_name\":\"grouped1_0039\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0040\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-125,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0033\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-123,false,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0033\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-123,-126,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0033\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-124,-126,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24],\"right\":[25],\"left_name\":\"grouped1_0044\",\"right_name\":\"grouped1_0048\",\"joined_name\":\"grouped1_0045\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26],\"right\":[27],\"left_name\":\"grouped1_0049\",\"right_name\":\"grouped1_0051\",\"joined_name\":\"grouped1_0050\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-101,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25],\"right\":[26,27],\"left_name\":\"grouped1_0045\",\"right_name\":\"grouped1_0050\",\"joined_name\":\"grouped1_0046\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-131,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25],\"right\":[26,27],\"left_name\":\"grouped1_0045\",\"right_name\":\"grouped1_0050\",\"joined_name\":\"grouped1_0046\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-130,false,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28],\"right\":[29],\"left_name\":\"grouped1_0052\",\"right_name\":\"grouped1_0055\",\"joined_name\":\"grouped1_0053\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28,29],\"right\":[30,31],\"left_name\":\"grouped1_0053\",\"right_name\":\"grouped1_0056\",\"joined_name\":\"grouped1_0054\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-133,false,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25,26,27],\"right\":[28,29,30,31],\"left_name\":\"grouped1_0046\",\"right_name\":\"grouped1_0054\",\"joined_name\":\"grouped1_0047\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-134,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25,26,27],\"right\":[28,29,30,31],\"left_name\":\"grouped1_0046\",\"right_name\":\"grouped1_0054\",\"joined_name\":\"grouped1_0047\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-132,-134,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-127,-135,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-127,-136,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0034\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-128,-135,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0034\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-129,-135,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],\"right\":[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-118,-139,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],\"right\":[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-119,-138,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],\"right\":[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-120,-137,140],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[39,59,61,65,66],\"full_literals\":[-141,35,55,57,60,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[58,60,69,70],\"full_literals\":[-142,54,56,64,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[34,48,49,76],\"full_literals\":[-143,30,44,45,71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,36,37,42,43,44,50,51,52,53],\"full_literals\":[-144,31,32,33,38,39,40,46,47,48,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[33,57,74],\"full_literals\":[-145,29,53,69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[38,45,46,47],\"full_literals\":[-146,34,41,42,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[40,63,80,81],\"full_literals\":[-147,36,58,74,75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[55,71,72,78,85],\"full_literals\":[-148,51,66,67,73,79]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[32,56,73,75],\"full_literals\":[-149,28,52,68,70]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-150,141,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-150,false,142],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0063\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-151,143,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0063\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-151,false,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0059\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-152,150,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0059\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-152,false,151],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0065\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0066\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-153,145,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0065\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0066\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-154,145,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0065\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0066\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-154,false,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0071\",\"right_name\":\"grouped2_0073\",\"joined_name\":\"grouped2_0072\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-155,148,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0071\",\"right_name\":\"grouped2_0073\",\"joined_name\":\"grouped2_0072\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-155,false,149],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0069\",\"right_name\":\"grouped2_0072\",\"joined_name\":\"grouped2_0070\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-156,147,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0069\",\"right_name\":\"grouped2_0072\",\"joined_name\":\"grouped2_0070\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-156,false,155],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0066\",\"right_name\":\"grouped2_0070\",\"joined_name\":\"grouped2_0067\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-157,153,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0066\",\"right_name\":\"grouped2_0070\",\"joined_name\":\"grouped2_0067\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-157,154,156],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0066\",\"right_name\":\"grouped2_0070\",\"joined_name\":\"grouped2_0067\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-158,154,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0067\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-159,152,158],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0067\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-159,false,157],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":41,\"full_literals\":[-37,160]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":54,\"full_literals\":[-50,160]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-59,161]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-72,161]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-78,162]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-81,163]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-62,164]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-63,164]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-76,165]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-80,166]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-82,166]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0077\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0078\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-162,167],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0077\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0078\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-161,false,167],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0077\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0078\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-161,-162,168],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-167,169],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-168,170],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-160,false,169],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-160,-167,170],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0080\",\"right_name\":\"grouped3_0083\",\"joined_name\":\"grouped3_0081\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-163,false,171],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0080\",\"right_name\":\"grouped3_0083\",\"joined_name\":\"grouped3_0081\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-163,-164,172],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0084\",\"right_name\":\"grouped3_0086\",\"joined_name\":\"grouped3_0085\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-166,173],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0084\",\"right_name\":\"grouped3_0086\",\"joined_name\":\"grouped3_0085\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-165,false,173],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0081\",\"right_name\":\"grouped3_0085\",\"joined_name\":\"grouped3_0082\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-171,false,174],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0081\",\"right_name\":\"grouped3_0085\",\"joined_name\":\"grouped3_0082\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-171,-173,175],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0081\",\"right_name\":\"grouped3_0085\",\"joined_name\":\"grouped3_0082\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-172,false,175],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0075\",\"right_name\":\"grouped3_0082\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-169,-175,176],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0075\",\"right_name\":\"grouped3_0082\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-170,-174,176],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[6,16,28,29,46,53,64,66,70,71,73,76,81,87]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[6,23,27,28,46,53,63,64,66,70,73,76,85,87]},{\"tag\":\"edge\",\"edge\":15,\"owners\":[6,9,28,33,37,41,47,49,52,53,54,74,77,84]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[21,41,49,54,60,64,69,70,77,84,87]}]}"
  "260 157 0 227 226 0\n261 153 0 260 222 0\n262 59 81 37 50 56 45 64 65 72 78 0 259 104 0\n263 169 0 242 244 239 240 228 229 232 230 231 106 107 105 120 108 262 0\n264 -175 0 263 255 253 0\n265 -172 0 264 252 0\n266 72 78 81 0 117 110 119 109 116 112 111 262 0\n267 -72 45 0 227 33 34 35 36 37 38 204 202 216 211 224 214 225 0\n268 81 0 227 109 267 266 47 48 49 50 118 202 4 5 6 211 205 214 217 225 224 0\n269 -29 0 268 55 0\n270 -33 0 268 56 0\n271 -37 0 268 57 0\n272 -53 0 268 58 0\n273 -54 0 268 59 0\n274 -56 0 268 60 0\n275 -64 0 268 61 0\n276 -69 0 268 62 0\n277 -72 0 268 63 0\n278 59 0 268 120 0\n279 163 0 268 233 0\n280 -145 0 276 269 272 204 0\n281 -52 0 278 11 0\n282 161 0 278 230 0\n283 171 0 279 246 0\n284 -164 0 279 265 247 0\n285 146 0 280 261 215 0\n286 -154 0 280 216 0\n287 167 0 282 240 0\n288 174 0 283 250 0\n289 -173 0 283 264 251 0\n290 -62 0 284 234 0\n291 -63 0 284 235 0\n292 156 0 286 260 223 0\n293 -158 0 286 224 0\n294 -170 0 288 255 254 0\n295 -166 0 289 248 0\n296 -165 0 289 249 0\n297 -77 0 291 121 0\n298 147 0 292 220 0\n299 155 0 292 221 0\n300 152 0 293 227 225 0\n301 -168 0 294 243 0\n302 -160 0 294 287 245 0\n303 -80 0 295 237 0\n304 -82 0 295 238 0\n305 -76 0 296 236 0\n306 148 0 299 218 0\n307 149 0 299 219 0\n308 150 0 300 213 0\n309 151 0 300 214 0\n310 -162 0 301 282 241 0\n311 -50 0 302 229 0\n312 141 0 308 209 0\n313 142 0 308 210 0\n314 143 0 309 211 0\n315 144 0 309 212 0\n316 -78 0 310 232 0\n317 65 0 313 273 275 274 201 0\n318 -16 0 317 16 0\n319 -30 0 317 17 0\n320 -43 0 317 18 0\n321 -44 0 317 19 0\n322 -45 0 317 20 0\n323 71 0 322 319 314 321 202 0\n324 -15 0 323 27 0\n325 -35 0 323 28 0\n326 -51 0 323 29 0\n327 -55 0 323 30 0\n328 -67 0 323 31 0\n329 -70 0 323 32 0\n330 118 0 274 272 324 318 325 319 311 322 271 269 305 323 320 297 169 170 167 168 155 157 166 162 152 153 146 147 164 165 160 161 150 151 148 149 144 145 143 134 133 132 131 129 128 127 126 125 124 122 69 73 72 66 83 81 74 0\n331 -139 0 330 199 196 0\n332 117 125 0 274 272 324 318 307 281 329 326 328 306 298 327 312 325 304 297 311 322 320 271 269 276 268 323 317 278 179 137 178 138 96 167 168 166 162 163 164 165 160 161 159 134 133 132 131 130 69 97 98 208 114 90 25 26 40 41 92 207 206 200 100 113 95 89 84 91 256 0\n333 7 0 277 276 311 316 322 320 271 270 269 82 83 84 87 258 0\n334 -38 0 333 1 0\n335 89 0 333 128 0\n336 26 0 333 276 277 316 86 0\n337 -20 0 333 317 85 0\n338 107 0 335 151 0\n339 102 0 336 141 0\n340 108 0 338 152 0\n341 133 0 339 188 0\n342 110 0 340 155 0\n343 134 0 341 189 0\n344 135 0 343 190 0\n345 -129 0 344 331 195 0\n346 58 -61 119 0 318 324 272 274 329 307 297 334 338 320 305 342 270 340 269 319 325 271 281 298 326 328 306 268 323 317 278 336 333 172 158 146 145 124 147 143 122 144 125 64 142 123 65 171 167 166 165 133 168 163 159 130 156 154 148 127 164 134 69 208 26 81 89 41 40 76 206 54 99 207 256 0\n347 -61 119 0 318 324 272 274 329 281 307 297 334 338 320 305 342 270 340 269 319 325 271 326 328 306 268 323 317 278 336 333 172 158 146 145 124 147 143 122 144 125 64 142 123 65 171 167 166 165 133 168 163 159 130 156 154 148 127 164 134 69 208 26 81 89 40 346 24 45 97 207 78 257 0\n348 119 0 340 342 345 271 325 270 319 269 274 272 324 318 307 281 329 323 327 298 326 328 306 172 158 171 146 147 167 168 332 144 145 142 143 166 162 180 125 124 123 122 164 161 183 65 134 131 69 208 26 40 41 347 103 136 175 177 174 135 75 93 206 207 54 0\n349 -138 0 348 199 197 0\n350 -128 0 349 344 194 0\n351 61 0 323 350 344 349 199 343 340 271 319 269 276 270 303 329 327 312 325 326 328 306 103 136 175 176 181 182 192 193 180 198 191 178 332 186 187 138 173 185 184 158 140 139 146 147 144 145 142 143 125 124 123 122 64 71 101 200 115 23 207 0\n352 -31 0 351 12 0\n353 -34 0 351 13 0\n354 -57 0 351 14 0\n355 -60 0 351 15 0\n356 -75 79 13 58 0 285 353 320 326 328 306 307 281 329 304 354 268 323 317 351 278 336 333 315 334 270 352 42 43 44 46 99 205 207 2 3 67 68 208 100 88 256 203 0\n357 73 75 79 58 0 304 303 351 326 328 306 298 307 281 329 102 207 22 206 41 79 208 0\n358 -73 0 307 281 329 39 40 208 0\n359 79 13 58 0 358 356 357 0\n360 -79 58 0 298 51 53 54 206 0\n361 79 58 0 306 328 326 358 359 207 21 0\n362 58 0 360 361 0\n363 -32 0 362 7 0\n364 -39 0 362 8 0\n365 -46 0 362 9 0\n366 -48 0 362 10 0\n367 -66 0 362 24 0\n368 -75 0 362 45 0\n369 -14 0 362 278 70 0\n370 -28 0 362 351 77 0\n371 79 0 367 306 328 326 358 207 0\n372 25 0 368 358 329 351 303 304 102 0\n373 -40 0 369 337 326 281 273 290 275 80 0\n374 68 0 370 329 281 307 208 0\n375 -47 0 371 52 0\n376 23 0 371 355 115 0\n377 -41 0 372 371 94 0\n378 49 0 373 352 270 334 364 365 363 315 366 375 203 0\n379 -42 0 376 333 336 372 378 362 278 351 317 374 323 371 268 257 0\n380 0 379 377 320 353 285 205 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.l) :=
(.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.g)) :=
(.branch 1
 (.leaf ([]))
 (.leaf ([])))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record019
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f83d07c3c8eac68da2e87ac98e6358b61db0e8b86e4785e0f8f19a4e9c64d92e479c94e5554d52d475c362d4743dc8ea338f1364cd32cc73c2ccb2ac6b86d1b26c5b0ef0731e2749ca719c9715c3783d0f13c6c1722a4582e078e1346291a459195151544d0b41dc0e2328d1324e0b0ac1b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6db6db6db49249269a69269a4924924d3492492692492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 62), (facetIndex 64), (facetIndex 65), (facetIndex 70)]))
 (.leaf ([(facetIndex 46), (facetIndex 66), (facetIndex 68), (facetIndex 72), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 44), (facetIndex 49), (facetIndex 59), (facetIndex 77)]))
 (.leaf ([(facetIndex 31), (facetIndex 38), (facetIndex 40), (facetIndex 60), (facetIndex 79)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 43), (facetIndex 45), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 51), (facetIndex 58), (facetIndex 74), (facetIndex 75), (facetIndex 92)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 47), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 29), (facetIndex 35), (facetIndex 42), (facetIndex 52), (facetIndex 55), (facetIndex 76), (facetIndex 78)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "50000000007d7b49001040003576f27a10c629eb0f6f056b8z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 61), (facetIndex 67)]))
 (.leaf ([(facetIndex 71), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 85)]))
 (.branch 4
 (.leaf ([(facetIndex 89)]))
 (.leaf ([(facetIndex 39), (facetIndex 48), (facetIndex 50)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 63), (facetIndex 69), (facetIndex 81)]))
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 86)])))
 (.branch 8
 (.leaf ([(facetIndex 84), (facetIndex 88), (facetIndex 91)]))
 (.branch 9
 (.leaf ([(facetIndex 87), (facetIndex 90)]))
 (.leaf ([(facetIndex 93), (facetIndex 94)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "99078378627665100000000105000005000000000000404000000004z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7]
def grouped2_0008 : List Nat := [7]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3, 4]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8, 9]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9]
def grouped3_0027 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record019" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record019" 74

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record019" "{\"ridges\":[[7,146],[11,770],[21,193],[21,208],[22,224],[34,146],[40,769],[43,146],[48,202],[49,770],[51,146],[51,162],[52,208],[53,146],[54,770],[55,224],[57,769],[64,208],[66,224],[70,193],[70,208],[72,224],[74,208],[74,224],[87,184],[93,180],[94,184]],\"owners\":[[7,146,[82,83,87,88,91],[34,43,51,52,53]],[34,146,[87,88,91],[7,43,51,52,53,82,83]],[43,146,[82,83,91],[7,34,51,52,53,87,88]],[51,146,[83,88],[7,34,43,52,53,82,87,91]],[53,146,[82,83,87,88,91],[7,34,43,51,52]],[51,162,[84,90],[9,36,47,55,56,82,87,91]],[40,769,[71],[11,49,54,57,61,67]],[57,769,[61,71],[11,40,49,54,67]],[11,770,[80,85,89],[40,49,54,57]],[49,770,[85],[11,40,54,57,80,89]],[54,770,[80,85],[11,40,49,57,89]],[21,193,[22,39,48,55,66,72],[52,64,70]],[70,193,[22,39,55,66],[21,48,52,64,72]],[21,208,[83,88,91,93,94],[52,64,70,74]],[52,208,[93,94],[21,64,70,74,83,88,91]],[64,208,[88,91,94],[21,52,70,74,83,93]],[70,208,[83,91,93],[21,52,64,74,88,94]],[74,208,[83,88],[21,52,64,70,91,93,94]],[22,224,[84,90,91,93,94],[55,66,72,74]],[55,224,[93,94],[22,66,72,74,84,90,91]],[66,224,[90,91,94],[22,55,72,74,84,93]],[72,224,[84,91,93],[22,55,66,74,90,94]],[74,224,[84,90],[22,55,66,72,91,93,94]],[48,202,[88,90],[]],[93,180,[63,82],[]],[87,184,[69,94],[]],[94,184,[69,87],[]]],\"edges\":[[32,[7,21,34,43,51,52,53,63,64,69,70,74,82,83,87,88,91,93,94]],[39,[21,22,39,48,52,55,64,66,70,72,74,83,84,88,90,91,93,94]],[44,[11,40,49,54,57,61,67,71,80,85,89]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record019" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record019\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-5],[-9,-8],[-11,-5],[-12,-9],[-22,-5],[-29,-12],[-33,-5],[-34,-9],[-35,-9],[-38,-8],[-38,-12],[-38,-34],[-38,-35],[-42,-5],[-42,-8],[-42,-12],[-42,-34],[-42,-35],[-45,-6],[-45,-11],[-45,-22],[-45,-33],[-46,-5],[-46,-45],[-1,37,38,41,42,45],[-7,41,42,45],[-13,37,38,45],[-16,38,42],[-18,37,38,41,42,45],[-16,39,44],[-10,30],[-21,23,30],[-2,36,40,43],[-15,40],[-19,36,40],[-3,4,9,14,20,26,31],[-29,4,9,20,26],[-3,38,42,45,47,48],[-17,47,48],[-25,42,45,48],[-29,38,45,47],[-32,38,42],[-4,39,44,45,47,48],[-20,47,48],[-26,44,45,48],[-31,39,45,47],[-32,39,44],[-14,42,44],[-47,24,37],[-41,28,48],[-48,28,41],[-49,6,11,16,22,32,33,46],[-50,5,8,12,17,20,34,35],[-51,49],[-52,50],[-53,51],[-53,52],[-54,53],[54],[-23,55],[-27,55],[-30,56],[-36,56],[-40,57],[-43,58],[-24,59],[-28,59],[-37,60],[-38,60],[-39,61],[-42,61],[-45,61],[-41,62],[-44,62],[-63,47,48],[-47,63],[-48,63],[-56,64],[-55,64],[-58,65],[-65,66],[-57,66],[-66,67],[-64,67],[-60,68],[-59,68],[-63,69],[-62,69],[-62,-63,70],[-69,71],[-70,72],[-61,71],[-72,73],[-68,-71,73],[-67,-73,74],[-74],[1,3,7,13,16,17,18,24,25,28,29,32,37,38,41,42,45,47,48],[3,4,9,14,17,20,25,26,29,31,32,38,39,42,44,45,47,48],[2,10,15,19,21,23,27,30,36,40,43]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":32,\"b\":29},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":29},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":58,\"b\":29},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":75,\"b\":29},{\"tag\":\"incompatible\",\"a\":76,\"b\":39},{\"tag\":\"incompatible\",\"a\":78,\"b\":39},{\"tag\":\"incompatible\",\"a\":83,\"b\":35},{\"tag\":\"incompatible\",\"a\":83,\"b\":42},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":78},{\"tag\":\"incompatible\",\"a\":88,\"b\":29},{\"tag\":\"incompatible\",\"a\":88,\"b\":35},{\"tag\":\"incompatible\",\"a\":88,\"b\":42},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":78},{\"tag\":\"incompatible\",\"a\":91,\"b\":32},{\"tag\":\"incompatible\",\"a\":91,\"b\":41},{\"tag\":\"incompatible\",\"a\":91,\"b\":58},{\"tag\":\"incompatible\",\"a\":91,\"b\":75},{\"tag\":\"incompatible\",\"a\":92,\"b\":29},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"mate\",\"ridge\":146,\"a\":7,\"owners\":[82,83,87,88,91]},{\"tag\":\"mate\",\"ridge\":146,\"a\":34,\"owners\":[87,88,91]},{\"tag\":\"mate\",\"ridge\":146,\"a\":43,\"owners\":[82,83,91]},{\"tag\":\"mate\",\"ridge\":146,\"a\":51,\"owners\":[83,88]},{\"tag\":\"mate\",\"ridge\":146,\"a\":53,\"owners\":[82,83,87,88,91]},{\"tag\":\"mate\",\"ridge\":162,\"a\":51,\"owners\":[84,90]},{\"tag\":\"mate\",\"ridge\":769,\"a\":40,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":769,\"a\":57,\"owners\":[61,71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":11,\"owners\":[80,85,89]},{\"tag\":\"mate\",\"ridge\":770,\"a\":49,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":770,\"a\":54,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":193,\"a\":21,\"owners\":[22,39,48,55,66,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":70,\"owners\":[22,39,55,66]},{\"tag\":\"mate\",\"ridge\":208,\"a\":21,\"owners\":[83,88,91,93,94]},{\"tag\":\"mate\",\"ridge\":208,\"a\":52,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":208,\"a\":64,\"owners\":[88,91,94]},{\"tag\":\"mate\",\"ridge\":208,\"a\":70,\"owners\":[83,91,93]},{\"tag\":\"mate\",\"ridge\":208,\"a\":74,\"owners\":[83,88]},{\"tag\":\"mate\",\"ridge\":224,\"a\":22,\"owners\":[84,90,91,93,94]},{\"tag\":\"mate\",\"ridge\":224,\"a\":55,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":224,\"a\":66,\"owners\":[90,91,94]},{\"tag\":\"mate\",\"ridge\":224,\"a\":72,\"owners\":[84,91,93]},{\"tag\":\"mate\",\"ridge\":224,\"a\":74,\"owners\":[84,90]},{\"tag\":\"mate\",\"ridge\":202,\"a\":48,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":180,\"a\":93,\"owners\":[63,82]},{\"tag\":\"mate\",\"ridge\":184,\"a\":87,\"owners\":[69,94]},{\"tag\":\"mate\",\"ridge\":184,\"a\":94,\"owners\":[69,87]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[32,41,51,58,74,75,92],\"full_literals\":[-49,6,11,16,22,32,33,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[29,35,42,52,55,76,78],\"full_literals\":[-50,5,8,12,17,20,34,35]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-23,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-27,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-30,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-36,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-40,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-43,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":63,\"full_literals\":[-24,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":69,\"full_literals\":[-28,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-37,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-38,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-39,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-42,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-45,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-41,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":90,\"full_literals\":[-44,62]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[93,94],\"full_literals\":[-63,47,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":93,\"full_literals\":[-47,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":94,\"full_literals\":[-48,63]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-63,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-67,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":32,\"owners\":[7,21,34,43,51,52,53,63,64,69,70,74,82,83,87,88,91,93,94]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[21,22,39,48,52,55,64,66,70,72,74,83,84,88,90,91,93,94]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[11,40,49,54,57,61,67,71,80,85,89]}]}"
  "100 53 0 59 58 0\n101 51 0 100 56 0\n102 52 0 100 57 0\n103 49 0 101 54 0\n104 50 0 102 55 0\n105 67 0 83 84 81 82 78 79 80 64 62 63 60 61 65 34 31 32 33 35 99 0\n106 -73 0 105 96 95 0\n107 -72 0 106 93 0\n108 -70 0 107 91 0\n109 -63 68 0 108 86 66 85 68 49 67 75 89 51 73 0\n110 42 45 68 0 86 66 85 68 49 69 41 27 109 77 39 67 50 28 42 40 38 26 29 25 97 0\n111 -42 68 0 104 86 66 85 68 49 109 77 44 39 14 15 16 17 18 53 0\n112 68 0 103 85 69 111 28 42 110 19 20 21 22 24 52 0\n113 -71 0 112 106 94 0\n114 -69 0 113 90 0\n115 -61 0 113 92 0\n116 -63 0 114 87 0\n117 -62 0 114 88 0\n118 -39 0 115 70 0\n119 -42 0 115 71 0\n120 -45 0 115 72 0\n121 -47 0 116 76 0\n122 -48 0 116 77 0\n123 -44 0 117 74 0\n124 -31 0 118 120 121 46 0\n125 -16 0 118 123 30 0\n126 -32 0 118 123 47 0\n127 -4 0 118 123 120 121 122 43 0\n128 -14 0 119 123 48 0\n129 -26 0 120 123 122 45 0\n130 -25 0 120 119 122 40 0\n131 -17 0 122 121 39 0\n132 -20 0 122 121 44 0\n133 -5 0 126 125 103 1 3 5 7 23 52 0\n134 -8 0 122 121 120 123 119 118 126 124 132 131 128 127 130 129 2 10 36 37 98 0\n135 -12 0 122 121 120 123 119 118 126 124 132 131 128 127 130 129 4 6 11 36 98 0\n136 -34 0 122 121 120 123 119 118 126 124 132 131 128 127 130 129 8 12 36 37 98 0\n137 35 0 136 104 135 133 134 131 132 53 0\n138 -9 0 137 9 0\n139 -38 0 137 13 0\n140 -3 0 138 127 128 132 129 124 36 0\n141 -29 0 138 127 129 132 37 0\n142 0 140 141 129 130 127 128 131 132 138 124 126 139 118 119 123 120 121 122 98 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00031.record019
