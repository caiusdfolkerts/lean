module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00053Frames
public import GraphInputsRow24Part00053Leaves
public import GraphInputsRow24Part00053Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record043
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1cc4f1e272a9a719661d98e538ce4ba1e0f9e1e25c9a6539715351d58d534cd4b61d4743db0dc368d6338e938cc7362d4b32d2b26c3b61d4731d2785c5783d0f23c4f0bd64a2a1a19836079c1586896261951525194354341da0cc318e130ce0b22c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69a4db6924934924d24926924934d2692492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.branch 2
 (.leaf ([(facetIndex 1)]))
 (.leaf ([(facetIndex 2)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.leaf ([(facetIndex 4)])))
 (.branch 6
 (.leaf ([(facetIndex 5)]))
 (.leaf ([(facetIndex 6)])))))
 (.branch 10
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)]))))
 (.branch 12
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)])))
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)]))))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)]))))
 (.branch 19
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.leaf ([(facetIndex 18)])))
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.leaf ([(facetIndex 20)])))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)])))
 (.branch 24
 (.leaf ([(facetIndex 23)]))
 (.leaf ([(facetIndex 24)]))))
 (.branch 27
 (.branch 26
 (.leaf ([(facetIndex 25)]))
 (.leaf ([(facetIndex 26)])))
 (.branch 28
 (.leaf ([(facetIndex 27)]))
 (.leaf ([(facetIndex 28)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "1cdeb38bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 29
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 41), (facetIndex 48), (facetIndex 65), (facetIndex 78)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 40), (facetIndex 46), (facetIndex 47)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 54), (facetIndex 55), (facetIndex 57), (facetIndex 62)]))
 (.branch 4
 (.leaf ([(facetIndex 45), (facetIndex 60), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 38), (facetIndex 59), (facetIndex 63), (facetIndex 68)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 69), (facetIndex 75)]))
 (.leaf ([(facetIndex 37), (facetIndex 43), (facetIndex 49), (facetIndex 52), (facetIndex 53)])))
 (.branch 8
 (.leaf ([(facetIndex 56), (facetIndex 70)]))
 (.branch 9
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32)]))
 (.leaf ([(facetIndex 36), (facetIndex 50), (facetIndex 61), (facetIndex 76)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "950000754330042934027226609601130600104691108882z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 42), (facetIndex 64)]))
 (.branch 2
 (.leaf ([(facetIndex 71), (facetIndex 81)]))
 (.leaf ([(facetIndex 39), (facetIndex 44), (facetIndex 58)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 77), (facetIndex 79), (facetIndex 82)])))
 (.branch 6
 (.leaf ([(facetIndex 51)]))
 (.leaf ([(facetIndex 80)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10e8200db200000000080000a000020004z1d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0, 1, 2, 3, 4, 5, 6]
def grouped1_0001 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def grouped1_0003 : List Nat := [7]
def grouped1_0004 : List Nat := [7, 8, 9]
def grouped1_0005 : List Nat := [7, 8, 9, 10, 11, 12, 13]
def grouped1_0006 : List Nat := [8, 9]
def grouped1_0007 : List Nat := [10]
def grouped1_0008 : List Nat := [10, 11]
def grouped1_0009 : List Nat := [10, 11, 12, 13]
def grouped1_0010 : List Nat := [11]
def grouped1_0011 : List Nat := [12, 13]
def grouped1_0012 : List Nat := [14]
def grouped1_0013 : List Nat := [14, 15, 16]
def grouped1_0014 : List Nat := [14, 15, 16, 17, 18, 19, 20]
def grouped1_0015 : List Nat := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]
def grouped1_0016 : List Nat := [15]
def grouped1_0017 : List Nat := [15, 16]
def grouped1_0018 : List Nat := [16]
def grouped1_0019 : List Nat := [17]
def grouped1_0020 : List Nat := [17, 18]
def grouped1_0021 : List Nat := [17, 18, 19, 20]
def grouped1_0022 : List Nat := [18]
def grouped1_0023 : List Nat := [19]
def grouped1_0024 : List Nat := [19, 20]
def grouped1_0025 : List Nat := [20]
def grouped1_0026 : List Nat := [21]
def grouped1_0027 : List Nat := [21, 22]
def grouped1_0028 : List Nat := [21, 22, 23, 24]
def grouped1_0029 : List Nat := [21, 22, 23, 24, 25, 26, 27, 28]
def grouped1_0030 : List Nat := [22]
def grouped1_0031 : List Nat := [23]
def grouped1_0032 : List Nat := [23, 24]
def grouped1_0033 : List Nat := [24]
def grouped1_0034 : List Nat := [25]
def grouped1_0035 : List Nat := [25, 26]
def grouped1_0036 : List Nat := [25, 26, 27, 28]
def grouped1_0037 : List Nat := [26]
def grouped1_0038 : List Nat := [27]
def grouped1_0039 : List Nat := [27, 28]
def grouped1_0040 : List Nat := [28]
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
def grouped3_0061 : List Nat := [0, 1, 2]
def grouped3_0063 : List Nat := [1]
def grouped3_0064 : List Nat := [1, 2]
def grouped3_0065 : List Nat := [2]
def grouped3_0066 : List Nat := [3]
def grouped3_0067 : List Nat := [3, 4]
def grouped3_0068 : List Nat := [3, 4, 5, 6]
def grouped3_0069 : List Nat := [4]
def grouped3_0070 : List Nat := [5]
def grouped3_0071 : List Nat := [5, 6]
def grouped3_0072 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_matrix_checked

def leafCount : Nat := 41
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 8), (facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 46), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 11), (facetIndex 13), (facetIndex 21), (facetIndex 22), (facetIndex 47), (facetIndex 49), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 9), (facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 47), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 9), (facetIndex 20), (facetIndex 23), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 68), (facetIndex 73), (facetIndex 75), (facetIndex 78), (facetIndex 79)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 19), (facetIndex 20), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 8), (facetIndex 20), (facetIndex 25), (facetIndex 28), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 78), (facetIndex 79)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 19), (facetIndex 20), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 9), (facetIndex 20), (facetIndex 25), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 78), (facetIndex 79)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 10), (facetIndex 13), (facetIndex 26), (facetIndex 27), (facetIndex 46), (facetIndex 48), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 82)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 26), (facetIndex 27), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 82)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 26), (facetIndex 27), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 82)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 9), (facetIndex 16), (facetIndex 27), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 54), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 70), (facetIndex 73), (facetIndex 75), (facetIndex 79)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 27), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 60), (facetIndex 62), (facetIndex 65), (facetIndex 68), (facetIndex 70), (facetIndex 73), (facetIndex 75), (facetIndex 79)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 13), (facetIndex 18), (facetIndex 47), (facetIndex 53), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 18), (facetIndex 47), (facetIndex 53), (facetIndex 55), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 8), (facetIndex 14), (facetIndex 16), (facetIndex 18), (facetIndex 46), (facetIndex 53), (facetIndex 55), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 8), (facetIndex 12), (facetIndex 13), (facetIndex 18), (facetIndex 46), (facetIndex 53), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 23), (facetIndex 24), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 8), (facetIndex 14), (facetIndex 23), (facetIndex 24), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 9), (facetIndex 14), (facetIndex 23), (facetIndex 24), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 23), (facetIndex 24), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 9), (facetIndex 14), (facetIndex 23), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 75), (facetIndex 78), (facetIndex 82)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 9), (facetIndex 14), (facetIndex 23), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 67), (facetIndex 68), (facetIndex 73), (facetIndex 75), (facetIndex 78), (facetIndex 79)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 9), (facetIndex 14), (facetIndex 23), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 67), (facetIndex 68), (facetIndex 74), (facetIndex 75), (facetIndex 77), (facetIndex 78)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 14), (facetIndex 22), (facetIndex 23), (facetIndex 28), (facetIndex 47), (facetIndex 50), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 67), (facetIndex 72), (facetIndex 75), (facetIndex 78), (facetIndex 82)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 23), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 75), (facetIndex 78), (facetIndex 82)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 23), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 73), (facetIndex 75), (facetIndex 78), (facetIndex 79)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leaf0027 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 23), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 74), (facetIndex 75), (facetIndex 77), (facetIndex 78)]
theorem leaf0027_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0027 = true := by
  decide +kernel
theorem leaf0027_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0027 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0027_counts_checked
def leaf0028 : List (Fin data.count) := [(facetIndex 13), (facetIndex 22), (facetIndex 23), (facetIndex 28), (facetIndex 47), (facetIndex 50), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 72), (facetIndex 75), (facetIndex 78), (facetIndex 82)]
theorem leaf0028_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0028 = true := by
  decide +kernel
theorem leaf0028_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0028 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0028_counts_checked
def leaf0029 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 9), (facetIndex 13), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0029_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0029 = true := by
  decide +kernel
theorem leaf0029_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0029 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0029_counts_checked
def leaf0030 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 14), (facetIndex 16), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0030_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0030 = true := by
  decide +kernel
theorem leaf0030_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0030 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0030_counts_checked
def leaf0031 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 25), (facetIndex 28), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 78), (facetIndex 82)]
theorem leaf0031_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0031 = true := by
  decide +kernel
theorem leaf0031_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0031 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0031_counts_checked
def leaf0032 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 25), (facetIndex 28), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 78), (facetIndex 79)]
theorem leaf0032_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0032 = true := by
  decide +kernel
theorem leaf0032_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0032 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0032_counts_checked
def leaf0033 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 25), (facetIndex 28), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 74), (facetIndex 77), (facetIndex 78)]
theorem leaf0033_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0033 = true := by
  decide +kernel
theorem leaf0033_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0033 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0033_counts_checked
def leaf0034 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 21), (facetIndex 22), (facetIndex 46), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0034_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0034 = true := by
  decide +kernel
theorem leaf0034_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0034 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0034_counts_checked
def leaf0035 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 14), (facetIndex 16), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0035_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0035 = true := by
  decide +kernel
theorem leaf0035_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0035 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0035_counts_checked
def leaf0036 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 25), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 78), (facetIndex 82)]
theorem leaf0036_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0036 = true := by
  decide +kernel
theorem leaf0036_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0036 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0036_counts_checked
def leaf0037 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 25), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 78), (facetIndex 79)]
theorem leaf0037_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0037 = true := by
  decide +kernel
theorem leaf0037_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0037 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0037_counts_checked
def leaf0038 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 25), (facetIndex 28), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 74), (facetIndex 77), (facetIndex 78)]
theorem leaf0038_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0038 = true := by
  decide +kernel
theorem leaf0038_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0038 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0038_counts_checked
def leaf0039 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 21), (facetIndex 22), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 69), (facetIndex 72), (facetIndex 76), (facetIndex 78), (facetIndex 82)]
theorem leaf0039_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0039 = true := by
  decide +kernel
theorem leaf0039_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0039 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0039_counts_checked
def leaf0040 : List (Fin data.count) := [(facetIndex 13), (facetIndex 22), (facetIndex 25), (facetIndex 28), (facetIndex 47), (facetIndex 50), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 69), (facetIndex 72), (facetIndex 78), (facetIndex 82)]
theorem leaf0040_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0040 = true := by
  decide +kernel
theorem leaf0040_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0040 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0040_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 20
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
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (leaf0020))
 (.leaf (leaf0021)))
 (.branch 23
 (.leaf (leaf0022))
 (.branch 24
 (.leaf (leaf0023))
 (.leaf (leaf0024)))))
 (.branch 27
 (.branch 26
 (.leaf (leaf0025))
 (.leaf (leaf0026)))
 (.branch 28
 (.leaf (leaf0027))
 (.branch 29
 (.leaf (leaf0028))
 (.leaf (leaf0029))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (leaf0030))
 (.leaf (leaf0031)))
 (.branch 33
 (.leaf (leaf0032))
 (.branch 34
 (.leaf (leaf0033))
 (.leaf (leaf0034)))))
 (.branch 38
 (.branch 36
 (.leaf (leaf0035))
 (.branch 37
 (.leaf (leaf0036))
 (.leaf (leaf0037))))
 (.branch 39
 (.leaf (leaf0038))
 (.branch 40
 (.leaf (leaf0039))
 (.leaf (leaf0040))))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record043" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":20},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group\",\"kind\":1,\"index\":23},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":26},{\"tag\":\"group\",\"kind\":1,\"index\":27},{\"tag\":\"group\",\"kind\":1,\"index\":28},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0008\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0020\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0042\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0042\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0064\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0064\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0067\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0067\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0071\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0071\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0068\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0068\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0068\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record043" 182

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record043" "{\"ridges\":[[0,13],[1,19],[1,21],[3,69],[3,70],[4,26],[5,138],[6,521],[7,19],[7,49],[9,97],[10,193],[11,642],[12,13],[13,13],[13,261],[13,268],[15,100],[16,261],[16,289],[16,292],[17,261],[17,324],[19,385],[19,392],[20,648],[21,289],[21,321],[21,352],[22,448],[24,52],[25,100],[27,138],[27,642],[27,648],[28,100],[28,292],[28,324],[28,352],[29,11],[29,13],[29,14],[30,13],[30,14],[30,69],[30,70],[31,138],[32,7],[32,11],[32,14],[32,261],[32,268],[33,14],[34,69],[34,70],[37,69],[37,70],[37,194],[38,70],[38,261],[38,324],[39,261],[39,385],[40,26],[40,49],[42,289],[42,298],[43,194],[44,265],[45,392],[46,19],[46,49],[46,50],[46,98],[47,49],[47,50],[47,515],[47,529],[48,19],[48,641],[48,642],[49,97],[49,194],[50,352],[51,418],[52,448],[53,67],[53,193],[53,515],[53,641],[53,642],[54,13],[55,261],[55,268],[56,13],[56,21],[56,28],[56,521],[56,529],[56,536],[57,13],[57,265],[57,268],[57,292],[58,13],[58,193],[58,204],[59,268],[59,324],[60,13],[60,268],[60,392],[61,21],[62,21],[62,49],[62,52],[62,261],[62,289],[62,292],[63,324],[63,448],[64,312],[65,641],[65,648],[66,392],[66,448],[67,265],[67,385],[67,392],[67,521],[67,641],[67,648],[68,97],[68,193],[68,289],[68,352],[68,385],[68,448],[69,14],[69,26],[69,28],[69,50],[69,52],[70,14],[70,28],[70,536],[71,292],[71,298],[72,14],[72,70],[72,194],[72,204],[73,14],[73,70],[73,324],[73,330],[74,14],[74,268],[74,390],[74,392],[75,22],[75,50],[75,52],[75,70],[75,98],[75,100],[76,70],[76,352],[77,70],[77,324],[77,390],[78,26],[78,138],[78,530],[78,536],[78,642],[78,648],[79,138],[79,330],[80,418],[81,312],[82,204],[82,268],[82,324],[82,392],[82,448]],\"owners\":[[32,7,[1,2,3,35,37],[0,31,33,36,38,39]],[29,11,[4,5,6,43,44,45],[0,30,32,40,42]],[32,11,[4,5,6,40,43],[0,29,30,42,44,45]],[70,14,[0,29,30,31,32,71,72,73,74],[23,33,69]],[46,19,[1,4,8,41,48],[7,34]],[61,21,[1,12,35,55,56],[14,34,62]],[62,21,[1,12,34,35,56],[14,55,61]],[75,22,[1,23,35,70],[24,34]],[53,67,[3,9,30,34,38,44,46,50],[10,43,52]],[3,69,[15,17,58,59,61,63],[30,34,37]],[30,69,[15,17,61,63],[3,34,37,58,59]],[34,69,[15,17,58,59,63],[3,30,37,61]],[37,69,[15,17,59,61],[3,30,34,58,63]],[72,70,[3,25,34,38,75,76],[30,37,73,77]],[77,70,[3,25,30,34,75],[37,38,72,73,76]],[40,26,[23,26,78],[4,41,69]],[47,515,[6,11,33,53],[8,35]],[53,515,[6,8,33,35,47],[11]],[7,49,[14,54,61,62,64],[40,46,47]],[40,49,[14,61,62],[7,46,47,54,64]],[46,49,[14,54,62,64],[7,40,47,61]],[47,49,[14,54,61,62,64],[7,40,46]],[62,49,[7,40,46,47],[14,54,61,64]],[46,50,[24,69],[7,40,47,75]],[47,50,[24,69,75],[7,40,46]],[69,50,[7,46,47],[24,40,75]],[75,50,[7,40,47],[24,46,69]],[47,529,[18,56,65],[8,35,48]],[56,529,[8,47,48],[18,35,65]],[78,530,[8,35,47],[26,48,70]],[9,97,[15,21,61,68],[46,49]],[49,97,[15,21,61],[9,46,68]],[68,97,[9,15,46,61],[21,49]],[46,98,[25,76,80],[9,49,50,75]],[75,98,[9,49,50,80],[25,46,76]],[68,193,[10,37,43,53,58],[22,49,63,66]],[37,194,[79,80],[10,43,49,52,53,72,77]],[43,194,[77,80],[10,37,49,52,53,72,79]],[49,194,[72,77,79],[10,37,43,52,53,80]],[72,194,[10,49,52,53,80],[37,43,77,79]],[48,641,[20,67],[11,53,65]],[53,641,[20,65,67],[11,48]],[65,641,[11,53],[20,48,67]],[67,641,[11,48,53],[20,65]],[11,642,[27,78],[48,53]],[27,642,[11,48,53],[78]],[48,642,[27],[11,53,78]],[53,642,[27,78],[11,48]],[78,642,[11,53],[27,48]],[56,28,[23,69,81],[12,54,55,70]],[69,28,[12,55,56],[23,54,70,81]],[70,28,[12,54,55,81],[23,56,69]],[13,261,[16,17,36,38,39,62,63],[32,55,60]],[16,261,[13,17,32,38,39,55,60,63],[36,62]],[32,261,[16,17,62,63],[13,36,38,39,55,60]],[62,261,[13,17,32,38,39,60,63],[16,36,55]],[67,265,[13,32,42,44,55,57,59,64],[19,45,66]],[13,268,[71,73,74,81,82],[32,55,57,59,60]],[32,268,[81,82],[13,55,57,59,60,71,73,74]],[55,268,[71,73,74,82],[13,32,57,59,60,81]],[57,268,[73,74,82],[13,32,55,59,60,71,81]],[59,268,[71,74,81],[13,32,55,57,60,73,82]],[60,268,[71,73,81],[13,32,55,57,59,74,82]],[74,268,[13,55,57,59,81],[32,60,71,73,82]],[82,268,[13,32,55,57,71,81],[59,60,73,74]],[24,52,[14,54,61,62,81],[69,75]],[62,52,[24,69,75],[14,54,61,81]],[69,52,[14,61,62],[24,54,75,81]],[75,52,[14,54,62,81],[24,61,69]],[25,100,[15,28,61],[75]],[28,100,[15,25,61,75],[]],[75,100,[15,28],[25,61]],[16,289,[21,42,50,51,64,68],[36,57,62]],[21,289,[16,36,42,51,57,62,64],[50,68]],[62,289,[21,42,50,51,68],[16,36,57,64]],[68,289,[16,36,42,57,62,64],[21,50,51]],[16,292,[28,71,76,81],[36,57,62]],[28,292,[16,36,57,62,71,81],[76]],[57,292,[28,76],[16,36,62,71,81]],[62,292,[28,71,76],[16,36,57,81]],[71,292,[16,28,62],[36,57,76,81]],[21,321,[17,22,38,44,52,59,66],[50]],[28,324,[17,38,59,63,73,77,82],[76]],[59,324,[28,76,77],[17,38,63,73,82]],[63,324,[28,73,76],[17,38,59,77,82]],[82,324,[17,28,38,76],[59,63,73,77]],[56,536,[26,78],[18,65,70]],[70,536,[18,65],[26,56,78]],[78,536,[18,56],[26,65,70]],[19,392,[74,79,82],[45,60,66,67]],[45,392,[82],[19,60,66,67,74,79]],[60,392,[79],[19,45,66,67,74,82]],[66,392,[74],[19,45,60,67,79,82]],[67,392,[74,79,82],[19,45,60,66]],[74,392,[19,66,67],[45,60,79,82]],[82,392,[19,45,67],[60,66,74,79]],[20,648,[27,78],[65,67]],[27,648,[20,65,67],[78]],[65,648,[27],[20,67,78]],[67,648,[27,78],[20,65]],[78,648,[20,67],[27,65]],[21,352,[28,76,80],[50,68]],[28,352,[21,50,68,80],[76]],[50,352,[28],[21,68,76,80]],[68,352,[28,76],[21,50,80]],[76,352,[21,68],[28,50,80]],[22,448,[77,79,80,82],[52,63,66,68]],[52,448,[82],[22,63,66,68,77,79,80]],[63,448,[79,80],[22,52,66,68,77,82]],[66,448,[77,80],[22,52,63,68,79,82]],[68,448,[77,79,82],[22,52,63,66,80]],[82,448,[22,52,68,80],[63,66,77,79]],[74,390,[39,77],[]],[77,390,[39,74],[]],[42,298,[71],[]],[71,298,[42],[]],[73,330,[44,79],[]],[79,330,[44,73],[]],[51,418,[80],[]],[80,418,[51],[]],[72,204,[58,82],[]],[82,204,[58,72],[]],[64,312,[81],[]],[81,312,[64],[]]],\"edges\":[[28,[13,19,32,42,44,45,55,57,59,60,64,66,67,71,73,74,79,81,82]],[30,[7,14,24,40,46,47,54,61,62,64,69,75,81]],[35,[9,15,21,25,28,46,49,50,61,68,75,76,80]],[37,[16,21,28,36,42,50,51,57,62,64,68,71,76,80,81]],[42,[19,22,39,45,51,52,60,63,66,67,68,74,77,79,80,82]],[43,[11,20,27,48,53,65,67,78]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record043" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record043\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-31,-2],[-31,-30],[-33,-30],[-34,-33],[-35,-31],[-36,-5],[-36,-31],[-37,-15],[-37,-33],[-39,-33],[-39,-37],[-40,-31],[-40,-32],[-40,-33],[-40,-39],[-41,-2],[-41,-36],[-44,-40],[-45,-31],[-45,-39],[-46,-33],[-46,-39],[-46,-40],[-47,-37],[-47,-43],[-48,-2],[-48,-36],[-48,-47],[-49,-7],[-49,-36],[-49,-41],[-49,-48],[-50,-47],[-51,-33],[-51,-39],[-51,-40],[-51,-43],[-51,-45],[-51,-46],[-51,-47],[-51,-50],[-52,-33],[-52,-46],[-53,-33],[-53,-37],[-53,-39],[-53,-51],[-54,-32],[-54,-40],[-54,-42],[-54,-46],[-54,-49],[-54,-50],[-55,-33],[-55,-37],[-56,-31],[-56,-33],[-57,-5],[-57,-33],[-57,-34],[-57,-36],[-57,-41],[-57,-42],[-57,-55],[-57,-56],[-58,-18],[-58,-30],[-58,-33],[-58,-37],[-58,-39],[-58,-40],[-58,-41],[-58,-43],[-58,-55],[-59,-31],[-59,-32],[-59,-33],[-59,-39],[-59,-46],[-59,-56],[-60,-17],[-60,-58],[-60,-59],[-61,-40],[-61,-45],[-61,-56],[-61,-58],[-61,-59],[-62,-17],[-62,-30],[-62,-37],[-62,-55],[-62,-58],[-63,-3],[-63,-16],[-63,-37],[-63,-55],[-63,-56],[-63,-58],[-63,-60],[-63,-62],[-64,-22],[-64,-51],[-64,-58],[-65,-58],[-65,-61],[-66,-57],[-67,-31],[-67,-52],[-67,-60],[-68,-6],[-68,-32],[-68,-42],[-68,-44],[-68,-59],[-68,-66],[-69,-18],[-69,-39],[-69,-45],[-69,-50],[-69,-51],[-69,-53],[-69,-60],[-69,-64],[-69,-67],[-70,-2],[-70,-30],[-70,-36],[-70,-41],[-70,-55],[-70,-58],[-71,-34],[-71,-36],[-71,-41],[-71,-70],[-72,-33],[-72,-39],[-72,-40],[-72,-46],[-72,-51],[-72,-53],[-72,-58],[-72,-70],[-74,-31],[-74,-40],[-74,-46],[-74,-51],[-74,-52],[-74,-53],[-74,-59],[-74,-72],[-75,-51],[-75,-52],[-75,-59],[-75,-72],[-76,-3],[-76,-35],[-76,-37],[-76,-47],[-76,-62],[-76,-70],[-76,-72],[-77,-16],[-77,-29],[-77,-33],[-77,-39],[-77,-40],[-77,-46],[-77,-53],[-77,-62],[-77,-74],[-77,-75],[-77,-76],[-78,-32],[-78,-37],[-78,-39],[-78,-51],[-78,-72],[-78,-77],[-79,-7],[-79,-71],[-80,-31],[-80,-37],[-80,-39],[-80,-40],[-80,-44],[-80,-51],[-80,-52],[-80,-60],[-80,-67],[-80,-72],[-80,-77],[-82,-58],[-82,-70],[-83,-31],[-83,-32],[-83,-38],[-83,-40],[-83,-44],[-83,-45],[-83,-60],[-83,-61],[-83,-64],[-83,-67],[-33,2,3,4,36,38],[-30,5,6,7,44,45,46],[-33,5,6,7,41,44],[-1,-14,-59],[-1,-58,-59],[-13,-14,-31],[-13,-14,-59],[-14,-30,-57],[-14,-30,-59],[-14,-31,-55],[-14,-31,-57],[-14,-57,-59],[-30,-57,-61],[-31,-57,-58],[-57,-58,-59],[-71,1,30,31,32,33,72,73,74,75],[-30,-71,-74],[-31,-71,-75],[-33,-70,-73],[-33,-71,-73],[-34,-70,-73],[-47,2,5,9,42,49],[-2,-8,-49],[-62,2,13,36,56,57],[-63,2,13,35,36,57],[-2,-57,-63],[-76,2,24,36,71],[-54,4,10,31,35,39,45,47,51],[-4,16,18,59,60,62,64],[-31,16,18,62,64],[-35,16,18,59,60,64],[-38,16,18,60,62],[-73,4,26,35,39,76,77],[-78,4,26,31,35,76],[-4,-73,-76],[-31,-76,-78],[-35,-73,-77],[-38,-74,-76],[-39,-73,-76],[-41,24,27,79],[-5,-70,-79],[-6,-28,-80],[-6,-79,-80],[-28,-32,-80],[-32,-79,-80],[-48,7,12,34,54],[-54,7,9,34,36,48],[-7,-57,-68],[-8,15,55,62,63,65],[-41,15,62,63],[-47,15,55,63,65],[-48,15,55,62,63,65],[-63,8,41,47,48],[-47,25,70],[-48,25,70,76],[-70,8,47,48],[-76,8,41,48],[-48,19,57,66],[-57,9,48,49],[-79,9,36,48],[-10,16,22,62,69],[-50,16,22,62],[-69,10,16,47,62],[-47,26,77,81],[-76,10,50,51,81],[-69,11,38,44,54,59],[-11,-59,-69],[-54,-59,-69],[-38,80,81],[-44,78,81],[-50,73,78,80],[-73,11,50,53,54,81],[-49,21,68],[-54,21,66,68],[-66,12,54],[-68,12,49,54],[-12,28,79],[-28,12,49,54],[-49,28],[-54,28,79],[-79,12,54],[-57,24,70,82],[-70,13,56,57],[-71,13,55,56,82],[-14,17,18,37,39,40,63,64],[-17,14,18,33,39,40,56,61,64],[-33,17,18,63,64],[-63,14,18,33,39,40,61,64],[-14,-17,-40],[-14,-18,-63],[-14,-39,-63],[-17,-40,-56],[-68,14,33,43,45,56,58,60,65],[-45,-58,-68],[-14,72,74,75,82,83],[-33,82,83],[-56,72,74,75,83],[-58,74,75,83],[-60,72,75,82],[-61,72,74,82],[-75,14,56,58,60,82],[-83,14,33,56,58,72,82],[-25,15,55,62,63,82],[-63,25,70,76],[-70,15,62,63],[-76,15,55,63,82],[-26,16,29,62],[-29,16,26,62,76],[-76,16,29],[-16,-29,-76],[-17,22,43,51,52,65,69],[-22,17,37,43,52,58,63,65],[-63,22,43,51,52,69],[-69,17,37,43,58,63,65],[-22,-43,-63],[-43,-63,-69],[-17,29,72,77,82],[-29,17,37,58,63,72,82],[-58,29,77],[-63,29,72,77],[-72,17,29,63],[-29,-63,-72],[-22,18,23,39,45,53,60,67],[-29,18,39,60,64,74,78,83],[-60,29,77,78],[-64,29,74,77],[-83,18,29,39,77],[-18,-29,-74],[-29,-39,-83],[-29,-60,-78],[-29,-64,-74],[-57,27,79],[-71,19,66],[-79,19,57],[-20,-40,-69],[-40,-68,-69],[-20,75,80,83],[-46,83],[-61,80],[-67,75],[-68,75,80,83],[-75,20,67,68],[-83,20,46,68],[-21,28,79],[-28,21,66,68],[-66,28],[-68,28,79],[-79,21,68],[-22,29,77,81],[-29,22,51,69,81],[-51,29],[-69,29,77],[-77,22,69],[-23,78,80,81,83],[-53,83],[-64,80,81],[-67,78,81],[-69,78,80,83],[-83,23,53,69,81],[-75,40,78],[-78,40,75],[-43,72],[-72,43],[-74,45,80],[-80,45,74],[-52,81],[-81,52],[-73,59,83],[-83,59,73],[-59,-73,-83],[-65,82],[-82,65],[-8,84],[-12,85],[-16,86],[-17,87],[-19,88],[-21,89],[-22,90],[-23,91],[-24,92],[-26,93],[-27,94],[-28,95],[-29,96],[-84,97],[-85,98],[-98,99],[-99,100],[-97,-99,101],[-100,102],[-101,103],[-87,104],[-86,-87,105],[-104,106],[-105,107],[-88,108],[-89,109],[-109,110],[-108,-109,111],[-110,112],[-111,113],[-106,-110,113],[-106,-111,114],[-107,113],[-90,-91,115],[-92,116],[-116,117],[-115,118],[-94,119],[-93,119],[-96,120],[-95,120],[-95,-96,121],[-120,122],[-121,123],[-119,-121,124],[-123,125],[-124,126],[-117,-123,126],[-118,-122,126],[-118,-123,127],[-127,129],[-112,-125,128],[-112,-126,129],[-112,-127,130],[-113,-125,129],[-114,-125,130],[-130,131],[-102,-129,131],[-103,-128,131],[-131],[-132,34,42,49,66,79],[-79,132],[-133,35,36,41,47,48],[-47,133],[-48,133],[-134,30,55,56,58,63],[-63,134],[-135,46,61,67,68],[-68,135],[-136,39,60,64,69],[-69,136],[-137,70,76],[-70,137],[-138,38,44,50,53,54],[-54,138],[-139,57,71],[-57,139],[-140,31,32,33],[-33,140],[-141,37,51,62,77],[-77,141],[-142,132,133],[-143,132],[-143,133],[-132,-133,143],[-144,135,136],[-145,135],[-145,136],[-135,-136,145],[-146,134,145],[-147,134],[-146,144],[-147,145],[-134,-145,147],[-148,142],[-148,143,147],[-149,143],[-148,146],[-149,147],[-143,-147,149],[-150,137,138],[-151,137],[-151,138],[-137,-138,151],[-152,140,141],[-141,152],[-153,140],[-153,141],[-154,139,152],[-155,139,153],[-156,139],[-155,152],[-139,-152,155],[-156,153],[-157,150,156],[-157,151,155],[-158,151,156],[-157,154],[-158,155],[-151,-155,158],[-159,156],[-160,148,159],[-160,149,158],[-160,157],[-149,-158,161],[160],[-161],[-162,43,65],[-43,162],[-65,162],[-163,72,82],[-72,163],[-82,163],[-164,40,45,59],[-40,164],[-45,164],[-59,164],[-165,73,74,75],[-73,165],[-74,165],[-75,165],[-166,78,80,83],[-78,166],[-80,166],[-83,166],[-167,52],[-52,167],[-168,81],[-81,168],[-169,163,164],[-164,169],[-163,169],[-163,-164,170],[-171,162,169],[-169,171],[-162,171],[-162,-169,172],[-162,-170,173],[-166,174],[-175,165],[-165,174],[-175,166],[-165,-166,175],[-176,167,168],[-177,167],[-167,-168,177],[-177,179],[-174,178],[-179,175,176],[-174,-177,180],[-175,179],[-181,171,179],[-180,182],[-171,-179,182],[-172,-178,182],[-173,182],[181],[-182],[-9,-11,-12,-14,-47,-57,-63,-68,-69,-70,-73,-77,-79,-83],[-12,-14,-22,-23,-48,-50,-57,-63,-68,-70,-73,-77,-79,-83],[-10,-11,-12,-14,-48,-57,-63,-68,-69,-70,-73,-77,-79,-83],[-10,-21,-24,-29,-48,-54,-57,-61,-63,-69,-74,-76,-79,-80],[-9,-14,-20,-21,-47,-54,-57,-63,-69,-70,-73,-77,-79,-83],[-9,-21,-26,-29,-47,-54,-57,-61,-63,-69,-70,-74,-79,-80],[-10,-14,-20,-21,-48,-54,-57,-63,-69,-70,-73,-77,-79,-83],[-10,-21,-26,-29,-48,-54,-57,-61,-63,-69,-70,-74,-79,-80],[-11,-14,-27,-28,-47,-49,-57,-63,-68,-69,-70,-73,-77,-83],[-10,-14,-27,-28,-48,-54,-57,-63,-68,-69,-70,-73,-77,-83],[-9,-14,-27,-28,-47,-54,-57,-63,-68,-69,-70,-73,-77,-83],[-10,-17,-28,-29,-48,-54,-55,-61,-66,-69,-71,-74,-76,-80],[-10,-13,-28,-29,-48,-54,-61,-63,-66,-69,-71,-74,-76,-80],[-10,-13,-14,-19,-48,-54,-63,-68,-69,-70,-73,-77,-79,-83],[-10,-15,-17,-19,-48,-54,-56,-68,-69,-70,-73,-77,-79,-83],[-9,-15,-17,-19,-47,-54,-56,-68,-69,-70,-73,-77,-79,-83],[-9,-13,-14,-19,-47,-54,-63,-68,-69,-70,-73,-77,-79,-83],[-9,-14,-24,-25,-47,-54,-57,-63,-68,-69,-73,-77,-79,-83],[-9,-15,-24,-25,-47,-54,-57,-58,-68,-69,-73,-77,-79,-83],[-10,-15,-24,-25,-48,-54,-57,-58,-68,-69,-73,-77,-79,-83],[-10,-14,-24,-25,-48,-54,-57,-63,-68,-69,-73,-77,-79,-83],[-10,-15,-24,-29,-48,-54,-57,-58,-68,-69,-73,-76,-79,-83],[-10,-15,-24,-29,-48,-54,-57,-58,-68,-69,-74,-76,-79,-80],[-10,-15,-24,-29,-48,-54,-57,-58,-68,-69,-75,-76,-78,-79],[-15,-23,-24,-29,-48,-51,-54,-57,-58,-68,-73,-76,-79,-83],[-10,-14,-24,-29,-48,-54,-57,-63,-68,-69,-73,-76,-79,-83],[-10,-14,-24,-29,-48,-54,-57,-63,-68,-69,-74,-76,-79,-80],[-10,-14,-24,-29,-48,-54,-57,-63,-68,-69,-75,-76,-78,-79],[-14,-23,-24,-29,-48,-51,-54,-57,-63,-68,-73,-76,-79,-83],[-8,-9,-10,-14,-54,-57,-63,-68,-69,-70,-73,-77,-79,-83],[-9,-14,-15,-17,-47,-54,-57,-68,-69,-70,-73,-77,-79,-83],[-9,-14,-26,-29,-47,-54,-57,-63,-68,-69,-70,-73,-79,-83],[-9,-14,-26,-29,-47,-54,-57,-63,-68,-69,-70,-74,-79,-80],[-9,-14,-26,-29,-47,-54,-57,-63,-68,-69,-70,-75,-78,-79],[-9,-14,-22,-23,-47,-54,-57,-63,-68,-70,-73,-77,-79,-83],[-10,-14,-15,-17,-48,-54,-57,-68,-69,-70,-73,-77,-79,-83],[-10,-14,-26,-29,-48,-54,-57,-63,-68,-69,-70,-73,-79,-83],[-10,-14,-26,-29,-48,-54,-57,-63,-68,-69,-70,-74,-79,-80],[-10,-14,-26,-29,-48,-54,-57,-63,-68,-69,-70,-75,-78,-79],[-10,-14,-22,-23,-48,-54,-57,-63,-68,-70,-73,-77,-79,-83],[-14,-23,-26,-29,-48,-51,-54,-57,-63,-68,-70,-73,-79,-83],[14,20,33,43,45,46,56,58,60,61,65,67,68,72,74,75,80,82,83],[8,15,25,41,47,48,55,62,63,65,70,76,82],[10,16,22,26,29,47,50,51,62,69,76,77,81],[17,22,29,37,43,51,52,58,63,65,69,72,77,81,82],[20,23,40,46,52,53,61,64,67,68,69,75,78,80,81,83],[12,21,28,49,54,66,68,79]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":20,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group\",\"index\":23,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":26,\"kind\":1},{\"tag\":\"group\",\"index\":27,\"kind\":1},{\"tag\":\"group\",\"index\":28,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":30,\"b\":1},{\"tag\":\"incompatible\",\"a\":30,\"b\":29},{\"tag\":\"incompatible\",\"a\":32,\"b\":29},{\"tag\":\"incompatible\",\"a\":33,\"b\":32},{\"tag\":\"incompatible\",\"a\":34,\"b\":30},{\"tag\":\"incompatible\",\"a\":35,\"b\":4},{\"tag\":\"incompatible\",\"a\":35,\"b\":30},{\"tag\":\"incompatible\",\"a\":36,\"b\":14},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":1},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":32},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":36},{\"tag\":\"incompatible\",\"a\":46,\"b\":42},{\"tag\":\"incompatible\",\"a\":47,\"b\":1},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":6},{\"tag\":\"incompatible\",\"a\":48,\"b\":35},{\"tag\":\"incompatible\",\"a\":48,\"b\":40},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":32},{\"tag\":\"incompatible\",\"a\":50,\"b\":38},{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":32},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":38},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":31},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":53,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":32},{\"tag\":\"incompatible\",\"a\":54,\"b\":36},{\"tag\":\"incompatible\",\"a\":55,\"b\":30},{\"tag\":\"incompatible\",\"a\":55,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":4},{\"tag\":\"incompatible\",\"a\":56,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":33},{\"tag\":\"incompatible\",\"a\":56,\"b\":35},{\"tag\":\"incompatible\",\"a\":56,\"b\":40},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":17},{\"tag\":\"incompatible\",\"a\":57,\"b\":29},{\"tag\":\"incompatible\",\"a\":57,\"b\":32},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":57,\"b\":38},{\"tag\":\"incompatible\",\"a\":57,\"b\":39},{\"tag\":\"incompatible\",\"a\":57,\"b\":40},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":30},{\"tag\":\"incompatible\",\"a\":58,\"b\":31},{\"tag\":\"incompatible\",\"a\":58,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":38},{\"tag\":\"incompatible\",\"a\":58,\"b\":45},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":16},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":39},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":57},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":16},{\"tag\":\"incompatible\",\"a\":61,\"b\":29},{\"tag\":\"incompatible\",\"a\":61,\"b\":36},{\"tag\":\"incompatible\",\"a\":61,\"b\":54},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":2},{\"tag\":\"incompatible\",\"a\":62,\"b\":15},{\"tag\":\"incompatible\",\"a\":62,\"b\":36},{\"tag\":\"incompatible\",\"a\":62,\"b\":54},{\"tag\":\"incompatible\",\"a\":62,\"b\":55},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":21},{\"tag\":\"incompatible\",\"a\":63,\"b\":50},{\"tag\":\"incompatible\",\"a\":63,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":30},{\"tag\":\"incompatible\",\"a\":66,\"b\":51},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":5},{\"tag\":\"incompatible\",\"a\":67,\"b\":31},{\"tag\":\"incompatible\",\"a\":67,\"b\":41},{\"tag\":\"incompatible\",\"a\":67,\"b\":43},{\"tag\":\"incompatible\",\"a\":67,\"b\":58},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":17},{\"tag\":\"incompatible\",\"a\":68,\"b\":38},{\"tag\":\"incompatible\",\"a\":68,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":52},{\"tag\":\"incompatible\",\"a\":68,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":1},{\"tag\":\"incompatible\",\"a\":69,\"b\":29},{\"tag\":\"incompatible\",\"a\":69,\"b\":35},{\"tag\":\"incompatible\",\"a\":69,\"b\":40},{\"tag\":\"incompatible\",\"a\":69,\"b\":54},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":70,\"b\":33},{\"tag\":\"incompatible\",\"a\":70,\"b\":35},{\"tag\":\"incompatible\",\"a\":70,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":32},{\"tag\":\"incompatible\",\"a\":71,\"b\":38},{\"tag\":\"incompatible\",\"a\":71,\"b\":39},{\"tag\":\"incompatible\",\"a\":71,\"b\":45},{\"tag\":\"incompatible\",\"a\":71,\"b\":50},{\"tag\":\"incompatible\",\"a\":71,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":30},{\"tag\":\"incompatible\",\"a\":73,\"b\":39},{\"tag\":\"incompatible\",\"a\":73,\"b\":45},{\"tag\":\"incompatible\",\"a\":73,\"b\":50},{\"tag\":\"incompatible\",\"a\":73,\"b\":51},{\"tag\":\"incompatible\",\"a\":73,\"b\":52},{\"tag\":\"incompatible\",\"a\":73,\"b\":58},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":50},{\"tag\":\"incompatible\",\"a\":74,\"b\":51},{\"tag\":\"incompatible\",\"a\":74,\"b\":58},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":75,\"b\":2},{\"tag\":\"incompatible\",\"a\":75,\"b\":34},{\"tag\":\"incompatible\",\"a\":75,\"b\":36},{\"tag\":\"incompatible\",\"a\":75,\"b\":46},{\"tag\":\"incompatible\",\"a\":75,\"b\":61},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":75,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":15},{\"tag\":\"incompatible\",\"a\":76,\"b\":28},{\"tag\":\"incompatible\",\"a\":76,\"b\":32},{\"tag\":\"incompatible\",\"a\":76,\"b\":38},{\"tag\":\"incompatible\",\"a\":76,\"b\":39},{\"tag\":\"incompatible\",\"a\":76,\"b\":45},{\"tag\":\"incompatible\",\"a\":76,\"b\":52},{\"tag\":\"incompatible\",\"a\":76,\"b\":61},{\"tag\":\"incompatible\",\"a\":76,\"b\":73},{\"tag\":\"incompatible\",\"a\":76,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":31},{\"tag\":\"incompatible\",\"a\":77,\"b\":36},{\"tag\":\"incompatible\",\"a\":77,\"b\":38},{\"tag\":\"incompatible\",\"a\":77,\"b\":50},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":6},{\"tag\":\"incompatible\",\"a\":78,\"b\":70},{\"tag\":\"incompatible\",\"a\":79,\"b\":30},{\"tag\":\"incompatible\",\"a\":79,\"b\":36},{\"tag\":\"incompatible\",\"a\":79,\"b\":38},{\"tag\":\"incompatible\",\"a\":79,\"b\":39},{\"tag\":\"incompatible\",\"a\":79,\"b\":43},{\"tag\":\"incompatible\",\"a\":79,\"b\":50},{\"tag\":\"incompatible\",\"a\":79,\"b\":51},{\"tag\":\"incompatible\",\"a\":79,\"b\":59},{\"tag\":\"incompatible\",\"a\":79,\"b\":66},{\"tag\":\"incompatible\",\"a\":79,\"b\":71},{\"tag\":\"incompatible\",\"a\":79,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":57},{\"tag\":\"incompatible\",\"a\":81,\"b\":69},{\"tag\":\"incompatible\",\"a\":82,\"b\":30},{\"tag\":\"incompatible\",\"a\":82,\"b\":31},{\"tag\":\"incompatible\",\"a\":82,\"b\":37},{\"tag\":\"incompatible\",\"a\":82,\"b\":39},{\"tag\":\"incompatible\",\"a\":82,\"b\":43},{\"tag\":\"incompatible\",\"a\":82,\"b\":44},{\"tag\":\"incompatible\",\"a\":82,\"b\":59},{\"tag\":\"incompatible\",\"a\":82,\"b\":60},{\"tag\":\"incompatible\",\"a\":82,\"b\":63},{\"tag\":\"incompatible\",\"a\":82,\"b\":66},{\"tag\":\"mate\",\"ridge\":7,\"a\":32,\"owners\":[1,2,3,35,37]},{\"tag\":\"mate\",\"ridge\":11,\"a\":29,\"owners\":[4,5,6,43,44,45]},{\"tag\":\"mate\",\"ridge\":11,\"a\":32,\"owners\":[4,5,6,40,43]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[0,13,58]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[0,57,58]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[12,13,30]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[12,13,58]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[13,29,56]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[13,29,58]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[13,30,54]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[13,30,56]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[13,56,58]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[29,56,60]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[30,56,57]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[56,57,58]},{\"tag\":\"mate\",\"ridge\":14,\"a\":70,\"owners\":[0,29,30,31,32,71,72,73,74]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[29,70,73]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[30,70,74]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[32,69,72]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[32,70,72]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[33,69,72]},{\"tag\":\"mate\",\"ridge\":19,\"a\":46,\"owners\":[1,4,8,41,48]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[1,7,48]},{\"tag\":\"mate\",\"ridge\":21,\"a\":61,\"owners\":[1,12,35,55,56]},{\"tag\":\"mate\",\"ridge\":21,\"a\":62,\"owners\":[1,12,34,35,56]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[1,56,62]},{\"tag\":\"mate\",\"ridge\":22,\"a\":75,\"owners\":[1,23,35,70]},{\"tag\":\"mate\",\"ridge\":67,\"a\":53,\"owners\":[3,9,30,34,38,44,46,50]},{\"tag\":\"mate\",\"ridge\":69,\"a\":3,\"owners\":[15,17,58,59,61,63]},{\"tag\":\"mate\",\"ridge\":69,\"a\":30,\"owners\":[15,17,61,63]},{\"tag\":\"mate\",\"ridge\":69,\"a\":34,\"owners\":[15,17,58,59,63]},{\"tag\":\"mate\",\"ridge\":69,\"a\":37,\"owners\":[15,17,59,61]},{\"tag\":\"mate\",\"ridge\":70,\"a\":72,\"owners\":[3,25,34,38,75,76]},{\"tag\":\"mate\",\"ridge\":70,\"a\":77,\"owners\":[3,25,30,34,75]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[3,72,75]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[30,75,77]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[34,72,76]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[37,73,75]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[38,72,75]},{\"tag\":\"mate\",\"ridge\":26,\"a\":40,\"owners\":[23,26,78]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[4,69,78]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[5,27,79]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[5,78,79]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[27,31,79]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[31,78,79]},{\"tag\":\"mate\",\"ridge\":515,\"a\":47,\"owners\":[6,11,33,53]},{\"tag\":\"mate\",\"ridge\":515,\"a\":53,\"owners\":[6,8,33,35,47]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[6,56,67]},{\"tag\":\"mate\",\"ridge\":49,\"a\":7,\"owners\":[14,54,61,62,64]},{\"tag\":\"mate\",\"ridge\":49,\"a\":40,\"owners\":[14,61,62]},{\"tag\":\"mate\",\"ridge\":49,\"a\":46,\"owners\":[14,54,62,64]},{\"tag\":\"mate\",\"ridge\":49,\"a\":47,\"owners\":[14,54,61,62,64]},{\"tag\":\"mate\",\"ridge\":49,\"a\":62,\"owners\":[7,40,46,47]},{\"tag\":\"mate\",\"ridge\":50,\"a\":46,\"owners\":[24,69]},{\"tag\":\"mate\",\"ridge\":50,\"a\":47,\"owners\":[24,69,75]},{\"tag\":\"mate\",\"ridge\":50,\"a\":69,\"owners\":[7,46,47]},{\"tag\":\"mate\",\"ridge\":50,\"a\":75,\"owners\":[7,40,47]},{\"tag\":\"mate\",\"ridge\":529,\"a\":47,\"owners\":[18,56,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":56,\"owners\":[8,47,48]},{\"tag\":\"mate\",\"ridge\":530,\"a\":78,\"owners\":[8,35,47]},{\"tag\":\"mate\",\"ridge\":97,\"a\":9,\"owners\":[15,21,61,68]},{\"tag\":\"mate\",\"ridge\":97,\"a\":49,\"owners\":[15,21,61]},{\"tag\":\"mate\",\"ridge\":97,\"a\":68,\"owners\":[9,15,46,61]},{\"tag\":\"mate\",\"ridge\":98,\"a\":46,\"owners\":[25,76,80]},{\"tag\":\"mate\",\"ridge\":98,\"a\":75,\"owners\":[9,49,50,80]},{\"tag\":\"mate\",\"ridge\":193,\"a\":68,\"owners\":[10,37,43,53,58]},{\"tag\":\"three\",\"ridge\":193,\"vertices\":[10,58,68]},{\"tag\":\"three\",\"ridge\":193,\"vertices\":[53,58,68]},{\"tag\":\"mate\",\"ridge\":194,\"a\":37,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":194,\"a\":43,\"owners\":[77,80]},{\"tag\":\"mate\",\"ridge\":194,\"a\":49,\"owners\":[72,77,79]},{\"tag\":\"mate\",\"ridge\":194,\"a\":72,\"owners\":[10,49,52,53,80]},{\"tag\":\"mate\",\"ridge\":641,\"a\":48,\"owners\":[20,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":53,\"owners\":[20,65,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":65,\"owners\":[11,53]},{\"tag\":\"mate\",\"ridge\":641,\"a\":67,\"owners\":[11,48,53]},{\"tag\":\"mate\",\"ridge\":642,\"a\":11,\"owners\":[27,78]},{\"tag\":\"mate\",\"ridge\":642,\"a\":27,\"owners\":[11,48,53]},{\"tag\":\"mate\",\"ridge\":642,\"a\":48,\"owners\":[27]},{\"tag\":\"mate\",\"ridge\":642,\"a\":53,\"owners\":[27,78]},{\"tag\":\"mate\",\"ridge\":642,\"a\":78,\"owners\":[11,53]},{\"tag\":\"mate\",\"ridge\":28,\"a\":56,\"owners\":[23,69,81]},{\"tag\":\"mate\",\"ridge\":28,\"a\":69,\"owners\":[12,55,56]},{\"tag\":\"mate\",\"ridge\":28,\"a\":70,\"owners\":[12,54,55,81]},{\"tag\":\"mate\",\"ridge\":261,\"a\":13,\"owners\":[16,17,36,38,39,62,63]},{\"tag\":\"mate\",\"ridge\":261,\"a\":16,\"owners\":[13,17,32,38,39,55,60,63]},{\"tag\":\"mate\",\"ridge\":261,\"a\":32,\"owners\":[16,17,62,63]},{\"tag\":\"mate\",\"ridge\":261,\"a\":62,\"owners\":[13,17,32,38,39,60,63]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[13,16,39]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[13,17,62]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[13,38,62]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[16,39,55]},{\"tag\":\"mate\",\"ridge\":265,\"a\":67,\"owners\":[13,32,42,44,55,57,59,64]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[44,57,67]},{\"tag\":\"mate\",\"ridge\":268,\"a\":13,\"owners\":[71,73,74,81,82]},{\"tag\":\"mate\",\"ridge\":268,\"a\":32,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":268,\"a\":55,\"owners\":[71,73,74,82]},{\"tag\":\"mate\",\"ridge\":268,\"a\":57,\"owners\":[73,74,82]},{\"tag\":\"mate\",\"ridge\":268,\"a\":59,\"owners\":[71,74,81]},{\"tag\":\"mate\",\"ridge\":268,\"a\":60,\"owners\":[71,73,81]},{\"tag\":\"mate\",\"ridge\":268,\"a\":74,\"owners\":[13,55,57,59,81]},{\"tag\":\"mate\",\"ridge\":268,\"a\":82,\"owners\":[13,32,55,57,71,81]},{\"tag\":\"mate\",\"ridge\":52,\"a\":24,\"owners\":[14,54,61,62,81]},{\"tag\":\"mate\",\"ridge\":52,\"a\":62,\"owners\":[24,69,75]},{\"tag\":\"mate\",\"ridge\":52,\"a\":69,\"owners\":[14,61,62]},{\"tag\":\"mate\",\"ridge\":52,\"a\":75,\"owners\":[14,54,62,81]},{\"tag\":\"mate\",\"ridge\":100,\"a\":25,\"owners\":[15,28,61]},{\"tag\":\"mate\",\"ridge\":100,\"a\":28,\"owners\":[15,25,61,75]},{\"tag\":\"mate\",\"ridge\":100,\"a\":75,\"owners\":[15,28]},{\"tag\":\"three\",\"ridge\":100,\"vertices\":[15,28,75]},{\"tag\":\"mate\",\"ridge\":289,\"a\":16,\"owners\":[21,42,50,51,64,68]},{\"tag\":\"mate\",\"ridge\":289,\"a\":21,\"owners\":[16,36,42,51,57,62,64]},{\"tag\":\"mate\",\"ridge\":289,\"a\":62,\"owners\":[21,42,50,51,68]},{\"tag\":\"mate\",\"ridge\":289,\"a\":68,\"owners\":[16,36,42,57,62,64]},{\"tag\":\"three\",\"ridge\":289,\"vertices\":[21,42,62]},{\"tag\":\"three\",\"ridge\":289,\"vertices\":[42,62,68]},{\"tag\":\"mate\",\"ridge\":292,\"a\":16,\"owners\":[28,71,76,81]},{\"tag\":\"mate\",\"ridge\":292,\"a\":28,\"owners\":[16,36,57,62,71,81]},{\"tag\":\"mate\",\"ridge\":292,\"a\":57,\"owners\":[28,76]},{\"tag\":\"mate\",\"ridge\":292,\"a\":62,\"owners\":[28,71,76]},{\"tag\":\"mate\",\"ridge\":292,\"a\":71,\"owners\":[16,28,62]},{\"tag\":\"three\",\"ridge\":292,\"vertices\":[28,62,71]},{\"tag\":\"mate\",\"ridge\":321,\"a\":21,\"owners\":[17,22,38,44,52,59,66]},{\"tag\":\"mate\",\"ridge\":324,\"a\":28,\"owners\":[17,38,59,63,73,77,82]},{\"tag\":\"mate\",\"ridge\":324,\"a\":59,\"owners\":[28,76,77]},{\"tag\":\"mate\",\"ridge\":324,\"a\":63,\"owners\":[28,73,76]},{\"tag\":\"mate\",\"ridge\":324,\"a\":82,\"owners\":[17,28,38,76]},{\"tag\":\"three\",\"ridge\":324,\"vertices\":[17,28,73]},{\"tag\":\"three\",\"ridge\":324,\"vertices\":[28,38,82]},{\"tag\":\"three\",\"ridge\":324,\"vertices\":[28,59,77]},{\"tag\":\"three\",\"ridge\":324,\"vertices\":[28,63,73]},{\"tag\":\"mate\",\"ridge\":536,\"a\":56,\"owners\":[26,78]},{\"tag\":\"mate\",\"ridge\":536,\"a\":70,\"owners\":[18,65]},{\"tag\":\"mate\",\"ridge\":536,\"a\":78,\"owners\":[18,56]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[19,39,68]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[39,67,68]},{\"tag\":\"mate\",\"ridge\":392,\"a\":19,\"owners\":[74,79,82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":45,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":60,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":392,\"a\":66,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":392,\"a\":67,\"owners\":[74,79,82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":74,\"owners\":[19,66,67]},{\"tag\":\"mate\",\"ridge\":392,\"a\":82,\"owners\":[19,45,67]},{\"tag\":\"mate\",\"ridge\":648,\"a\":20,\"owners\":[27,78]},{\"tag\":\"mate\",\"ridge\":648,\"a\":27,\"owners\":[20,65,67]},{\"tag\":\"mate\",\"ridge\":648,\"a\":65,\"owners\":[27]},{\"tag\":\"mate\",\"ridge\":648,\"a\":67,\"owners\":[27,78]},{\"tag\":\"mate\",\"ridge\":648,\"a\":78,\"owners\":[20,67]},{\"tag\":\"mate\",\"ridge\":352,\"a\":21,\"owners\":[28,76,80]},{\"tag\":\"mate\",\"ridge\":352,\"a\":28,\"owners\":[21,50,68,80]},{\"tag\":\"mate\",\"ridge\":352,\"a\":50,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":352,\"a\":68,\"owners\":[28,76]},{\"tag\":\"mate\",\"ridge\":352,\"a\":76,\"owners\":[21,68]},{\"tag\":\"mate\",\"ridge\":448,\"a\":22,\"owners\":[77,79,80,82]},{\"tag\":\"mate\",\"ridge\":448,\"a\":52,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":448,\"a\":63,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":448,\"a\":66,\"owners\":[77,80]},{\"tag\":\"mate\",\"ridge\":448,\"a\":68,\"owners\":[77,79,82]},{\"tag\":\"mate\",\"ridge\":448,\"a\":82,\"owners\":[22,52,68,80]},{\"tag\":\"mate\",\"ridge\":390,\"a\":74,\"owners\":[39,77]},{\"tag\":\"mate\",\"ridge\":390,\"a\":77,\"owners\":[39,74]},{\"tag\":\"mate\",\"ridge\":298,\"a\":42,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":298,\"a\":71,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":330,\"a\":73,\"owners\":[44,79]},{\"tag\":\"mate\",\"ridge\":330,\"a\":79,\"owners\":[44,73]},{\"tag\":\"mate\",\"ridge\":418,\"a\":51,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":418,\"a\":80,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":204,\"a\":72,\"owners\":[58,82]},{\"tag\":\"mate\",\"ridge\":204,\"a\":82,\"owners\":[58,72]},{\"tag\":\"three\",\"ridge\":204,\"vertices\":[58,72,82]},{\"tag\":\"mate\",\"ridge\":312,\"a\":64,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":312,\"a\":81,\"owners\":[64]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-8,84]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-12,85]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-16,86]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-17,87]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-19,88]},{\"tag\":\"group_take\",\"kind\":1,\"index\":20,\"member\":20,\"full_literals\":[-21,89]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-22,90]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-23,91]},{\"tag\":\"group_take\",\"kind\":1,\"index\":23,\"member\":23,\"full_literals\":[-24,92]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-26,93]},{\"tag\":\"group_take\",\"kind\":1,\"index\":26,\"member\":26,\"full_literals\":[-27,94]},{\"tag\":\"group_take\",\"kind\":1,\"index\":27,\"member\":27,\"full_literals\":[-28,95]},{\"tag\":\"group_take\",\"kind\":1,\"index\":28,\"member\":28,\"full_literals\":[-29,96]},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7,8,9],\"right\":[10,11,12,13],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-99,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7,8,9],\"right\":[10,11,12,13],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0005\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-97,-99,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-100,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-101,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-87,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-104,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-105,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-88,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18],\"right\":[19,20],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-109,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18],\"right\":[19,20],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-108,-109,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-110,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-111,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-106,-110,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-106,-111,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0014\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-107,false,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-90,-91,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23],\"right\":[24],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22],\"right\":[23,24],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-116,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22],\"right\":[23,24],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0028\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-115,false,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[27],\"right\":[28],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0039\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-96,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[27],\"right\":[28],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[27],\"right\":[28],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-95,-96,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0036\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-120,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0036\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-121,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0036\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-119,-121,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0029\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-123,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0029\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-124,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0029\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-117,-123,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0029\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-118,-122,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0029\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-118,-123,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0015\",\"a\":0,\"b\":4,\"direction\":\"forward\",\"full_literals\":[false,-127,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-112,-125,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-112,-126,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-112,-127,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0015\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-113,-125,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0015\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-114,-125,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13],\"right\":[14,15,16,17,18,19,20,21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":5,\"direction\":\"forward\",\"full_literals\":[false,-130,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13],\"right\":[14,15,16,17,18,19,20,21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-102,-129,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13],\"right\":[14,15,16,17,18,19,20,21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-103,-128,131],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[33,41,48,65,78],\"full_literals\":[-132,34,42,49,66,79]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":78,\"full_literals\":[-79,132]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[34,35,40,46,47],\"full_literals\":[-133,35,36,41,47,48]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":46,\"full_literals\":[-47,133]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":47,\"full_literals\":[-48,133]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[29,54,55,57,62],\"full_literals\":[-134,30,55,56,58,63]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":62,\"full_literals\":[-63,134]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[45,60,66,67],\"full_literals\":[-135,46,61,67,68]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":67,\"full_literals\":[-68,135]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[38,59,63,68],\"full_literals\":[-136,39,60,64,69]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":68,\"full_literals\":[-69,136]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[69,75],\"full_literals\":[-137,70,76]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":69,\"full_literals\":[-70,137]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[37,43,49,52,53],\"full_literals\":[-138,38,44,50,53,54]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":53,\"full_literals\":[-54,138]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[56,70],\"full_literals\":[-139,57,71]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":56,\"full_literals\":[-57,139]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[30,31,32],\"full_literals\":[-140,31,32,33]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":32,\"full_literals\":[-33,140]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[36,50,61,76],\"full_literals\":[-141,37,51,62,77]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":76,\"full_literals\":[-77,141]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-142,132,133],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-143,132,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-143,false,133],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-132,-133,143],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-144,135,136],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-145,135,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-145,false,136],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-135,-136,145],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-146,134,145],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-147,134,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-146,false,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-147,false,145],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-134,-145,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-148,142,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-148,143,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-149,143,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-148,false,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-149,false,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-143,-147,149],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-150,137,138],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-151,137,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-151,false,138],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-137,-138,151],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-152,140,141],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-141,152],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-153,140,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-153,false,141],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-154,139,152],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-155,139,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-156,139,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-155,false,152],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-139,-152,155],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-156,false,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-157,150,156],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-157,151,155],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-158,151,156],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-157,false,154],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-158,false,155],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-151,-155,158],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-159,false,156],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-160,148,159],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-160,149,158],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-160,false,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-149,-158,161],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[42,64],\"full_literals\":[-162,43,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":42,\"full_literals\":[-43,162]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-65,162]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[71,81],\"full_literals\":[-163,72,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-72,163]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-82,163]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[39,44,58],\"full_literals\":[-164,40,45,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":39,\"full_literals\":[-40,164]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":44,\"full_literals\":[-45,164]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":58,\"full_literals\":[-59,164]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[72,73,74],\"full_literals\":[-165,73,74,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-73,165]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-74,165]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-75,165]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[77,79,82],\"full_literals\":[-166,78,80,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-78,166]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-80,166]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-83,166]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[51],\"full_literals\":[-167,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":51,\"full_literals\":[-52,167]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[80],\"full_literals\":[-168,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-81,168]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0065\",\"joined_name\":\"grouped3_0064\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-169,163,164],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0065\",\"joined_name\":\"grouped3_0064\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-164,169],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0065\",\"joined_name\":\"grouped3_0064\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-163,false,169],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0065\",\"joined_name\":\"grouped3_0064\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-163,-164,170],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-171,162,169],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-169,171],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-162,false,171],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-162,-169,172],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-162,-170,173],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0067\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-166,174],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0067\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-175,165,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0067\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-165,false,174],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0067\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-175,false,166],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0067\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-165,-166,175],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0071\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-176,167,168],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0071\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-177,167,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0071\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-167,-168,177],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0068\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-177,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0068\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-174,false,178],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0068\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-179,175,176],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0068\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-174,-177,180],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0068\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-175,false,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-181,171,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-180,182],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-171,-179,182],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-172,-178,182],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-173,false,182],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[8,10,11,13,46,56,62,67,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[11,13,21,22,47,49,56,62,67,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[9,10,11,13,47,56,62,67,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[9,20,23,28,47,53,56,60,62,68,73,75,78,79]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[8,13,19,20,46,53,56,62,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[8,20,25,28,46,53,56,60,62,68,69,73,78,79]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[9,13,19,20,47,53,56,62,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[9,20,25,28,47,53,56,60,62,68,69,73,78,79]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[10,13,26,27,46,48,56,62,67,68,69,72,76,82]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[9,13,26,27,47,53,56,62,67,68,69,72,76,82]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[8,13,26,27,46,53,56,62,67,68,69,72,76,82]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[9,16,27,28,47,53,54,60,65,68,70,73,75,79]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[9,12,27,28,47,53,60,62,65,68,70,73,75,79]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[9,12,13,18,47,53,62,67,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[9,14,16,18,47,53,55,67,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[8,14,16,18,46,53,55,67,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[8,12,13,18,46,53,62,67,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[8,13,23,24,46,53,56,62,67,68,72,76,78,82]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[8,14,23,24,46,53,56,57,67,68,72,76,78,82]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[9,14,23,24,47,53,56,57,67,68,72,76,78,82]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[9,13,23,24,47,53,56,62,67,68,72,76,78,82]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[9,14,23,28,47,53,56,57,67,68,72,75,78,82]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[9,14,23,28,47,53,56,57,67,68,73,75,78,79]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[9,14,23,28,47,53,56,57,67,68,74,75,77,78]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[14,22,23,28,47,50,53,56,57,67,72,75,78,82]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[9,13,23,28,47,53,56,62,67,68,72,75,78,82]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[9,13,23,28,47,53,56,62,67,68,73,75,78,79]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[9,13,23,28,47,53,56,62,67,68,74,75,77,78]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[13,22,23,28,47,50,53,56,62,67,72,75,78,82]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[7,8,9,13,53,56,62,67,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[8,13,14,16,46,53,56,67,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[8,13,25,28,46,53,56,62,67,68,69,72,78,82]},{\"tag\":\"block\",\"leaf\":32,\"vertices\":[8,13,25,28,46,53,56,62,67,68,69,73,78,79]},{\"tag\":\"block\",\"leaf\":33,\"vertices\":[8,13,25,28,46,53,56,62,67,68,69,74,77,78]},{\"tag\":\"block\",\"leaf\":34,\"vertices\":[8,13,21,22,46,53,56,62,67,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":35,\"vertices\":[9,13,14,16,47,53,56,67,68,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":36,\"vertices\":[9,13,25,28,47,53,56,62,67,68,69,72,78,82]},{\"tag\":\"block\",\"leaf\":37,\"vertices\":[9,13,25,28,47,53,56,62,67,68,69,73,78,79]},{\"tag\":\"block\",\"leaf\":38,\"vertices\":[9,13,25,28,47,53,56,62,67,68,69,74,77,78]},{\"tag\":\"block\",\"leaf\":39,\"vertices\":[9,13,21,22,47,53,56,62,67,69,72,76,78,82]},{\"tag\":\"block\",\"leaf\":40,\"vertices\":[13,22,25,28,47,50,53,56,62,67,69,72,78,82]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[13,19,32,42,44,45,55,57,59,60,64,66,67,71,73,74,79,81,82]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[7,14,24,40,46,47,54,61,62,64,69,75,81]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[9,15,21,25,28,46,49,50,61,68,75,76,80]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[16,21,28,36,42,50,51,57,62,64,68,71,76,80,81]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[19,22,39,45,51,52,60,63,66,67,68,74,77,79,80,82]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[11,20,27,48,53,65,67,78]}]}"
  "602 -130 0 436 433 0\n603 157 0 502 500 0\n604 154 0 603 494 0\n605 -180 0 554 549 0\n606 -173 0 554 552 0\n607 -177 171 0 605 531 528 509 508 527 512 532 506 505 541 546 522 535 42 43 109 148 153 188 521 302 299 301 304 341 303 345 596 0\n608 -167 177 0 522 542 370 525 0\n609 -153 -14 56 -78 33 0 179 177 175 174 483 484 454 456 1 7 215 210 228 0\n610 -62 18 -14 39 37 64 40 0 89 101 289 0\n611 56 58 60 135 -75 -78 64 33 169 0 502 463 469 475 499 495 488 179 177 176 175 174 528 509 527 511 305 609 490 497 498 474 468 466 462 446 117 610 456 481 454 1 2 5 7 214 215 210 229 442 0\n612 -56 -158 -78 33 0 495 488 179 177 175 174 56 65 454 483 481 490 486 456 493 452 160 478 135 448 0\n613 -58 -155 77 51 37 32 -75 33 0 488 93 456 484 481 486 454 218 222 452 0\n614 135 -75 -78 64 33 171 0 502 179 177 175 174 607 608 523 371 531 528 509 508 532 506 505 463 469 475 499 495 612 613 611 81 100 123 334 316 599 0\n615 -67 -75 -78 64 33 0 502 179 177 176 175 174 108 110 125 454 446 483 464 490 469 497 475 498 499 474 495 612 466 488 613 481 456 90 92 101 442 0\n616 -62 63 -134 56 58 0 90 92 442 0\n617 63 -134 -152 -14 56 58 -78 33 0 179 177 175 174 616 456 481 454 2 214 442 0\n618 -63 -152 -14 77 51 37 32 64 33 0 95 101 294 456 234 481 454 0\n619 -155 -14 56 58 60 -75 -78 64 33 40 0 502 609 490 497 498 474 179 177 176 175 174 488 486 618 617 466 464 446 117 610 456 481 454 215 222 452 0\n620 -71 49 -132 -68 0 116 113 132 181 437 0\n621 63 71 -134 -14 56 58 -78 33 0 604 617 485 452 64 212 442 0\n622 -47 -26 -70 -79 -57 -63 -54 -69 -14 -68 -75 -78 0 230 58 52 179 356 113 226 588 0\n623 76 -79 -57 31 35 4 -63 -54 62 -69 -133 -137 -14 -68 -75 -78 0 62 61 95 179 356 448 238 622 267 439 593 0\n624 56 58 60 -68 -75 -78 64 38 83 171 0 603 502 604 116 114 113 179 177 176 175 174 531 528 509 300 359 607 608 523 371 527 513 512 511 532 506 505 297 619 495 492 499 478 479 473 475 459 460 467 469 464 446 117 120 356 610 450 52 620 621 95 618 233 235 234 485 452 60 61 62 230 437 623 159 231 269 439 582 0\n625 58 60 -68 -75 -78 64 38 83 171 0 502 604 603 114 179 177 176 175 174 531 528 509 300 359 532 506 505 624 56 65 98 612 454 499 473 475 459 469 464 446 120 318 89 456 481 488 485 492 452 479 620 450 52 0\n626 60 -68 -75 -78 64 38 83 171 0 603 502 604 116 114 113 179 177 176 175 174 531 528 509 300 359 625 72 74 93 99 131 323 613 456 495 492 499 478 479 473 475 448 459 460 469 157 159 240 310 314 464 454 446 481 120 267 485 450 52 620 452 60 61 286 437 439 578 0\n627 80 83 -179 0 554 550 531 527 513 372 528 509 300 342 607 608 523 371 524 540 545 538 536 508 512 532 506 505 273 343 360 368 518 514 175 177 179 614 615 444 626 81 82 100 123 334 316 599 0\n628 69 64 63 58 140 -80 171 0 502 192 189 187 184 183 607 608 523 371 531 528 509 508 532 506 505 446 464 469 475 499 495 488 481 456 89 316 322 599 0\n629 -57 -134 63 58 -68 44 46 45 0 111 58 64 65 252 442 206 0\n630 152 63 58 -68 44 46 45 0 604 603 502 488 485 495 492 499 478 473 475 459 460 467 629 452 133 134 135 620 448 32 157 159 439 0\n631 63 58 140 -68 77 51 44 37 46 171 0 607 608 523 371 531 528 509 508 527 512 532 506 505 630 481 456 89 316 318 322 599 0\n632 47 -70 -26 -79 -57 -54 -69 -133 35 -14 -29 -63 -68 -74 -80 0 62 61 101 95 267 439 592 0\n633 76 -79 -57 -54 -69 -133 -137 35 -14 -29 -63 -68 -74 -80 0 230 58 52 101 95 113 312 448 632 226 587 0\n634 58 -68 -80 33 53 46 171 0 604 603 502 182 112 454 116 113 531 527 512 369 192 189 187 186 184 183 607 608 523 371 528 508 513 532 506 505 631 95 98 101 324 297 332 335 618 235 236 488 485 495 492 499 478 479 473 475 459 460 469 464 446 120 450 52 620 452 60 61 62 230 437 633 159 269 231 439 581 0\n635 -68 -80 33 53 46 171 0 604 603 502 531 527 512 369 192 189 187 186 184 183 182 528 509 112 113 116 454 634 72 74 93 99 104 131 323 456 481 488 485 495 492 499 478 479 473 475 448 459 460 469 157 159 314 242 310 464 446 120 267 450 52 620 452 60 61 286 437 439 577 0\n636 -58 68 -74 77 67 60 51 44 39 37 31 33 53 46 0 502 87 93 104 131 444 456 463 484 469 490 475 497 499 498 495 493 474 488 478 479 468 481 448 462 454 242 446 48 120 450 0\n637 -32 68 -80 0 48 248 249 281 283 348 350 601 0\n638 28 66 79 49 54 68 0 281 348 601 0\n639 -69 -99 -109 -95 66 79 58 77 37 171 0 436 403 405 393 395 434 429 423 607 608 523 371 532 506 505 356 389 418 420 421 422 424 414 415 428 431 412 387 386 435 406 407 411 336 268 396 404 399 385 394 401 397 244 390 381 380 377 262 318 257 0\n640 -63 69 115 -74 77 67 60 51 39 53 171 0 607 608 523 531 528 508 527 512 532 505 324 317 332 327 383 384 410 0\n641 66 79 49 54 140 58 68 -80 53 171 0 436 531 527 512 369 192 190 189 187 184 183 607 608 523 371 528 509 508 532 506 505 638 388 282 349 417 378 382 419 391 402 392 403 393 405 395 434 429 425 413 639 640 628 102 335 315 599 0\n642 63 69 140 58 -80 171 0 531 527 512 369 192 187 183 607 608 523 371 528 509 508 532 506 505 628 102 335 315 599 0\n643 69 127 -95 140 58 -80 53 171 0 531 527 512 369 192 190 189 187 184 528 508 642 324 640 389 413 418 426 420 0\n644 -63 -69 54 140 77 60 51 44 37 53 0 603 120 117 95 101 456 236 481 450 488 479 492 0\n645 -66 54 140 58 -80 53 171 0 436 603 192 189 187 186 183 532 506 505 279 350 378 388 391 392 393 395 434 427 643 117 120 356 389 418 420 422 431 409 400 644 318 89 380 456 398 481 379 488 236 492 450 479 0\n646 -69 6 71 7 54 140 58 77 60 51 44 37 53 46 171 0 604 502 531 527 512 532 506 505 644 318 89 456 481 488 485 495 452 499 58 64 65 475 206 442 467 0\n647 -79 54 140 58 68 -80 53 46 171 0 436 531 527 512 369 192 190 189 187 186 184 183 528 508 180 181 247 285 352 378 382 391 402 392 403 393 405 395 434 429 646 642 324 640 389 413 416 425 419 0\n648 54 140 58 68 -80 53 46 171 0 602 192 189 187 186 183 532 506 505 645 647 641 29 277 283 382 246 388 402 403 405 430 643 356 644 646 389 318 337 418 380 381 420 397 401 422 399 404 432 408 0\n649 -71 79 -61 -134 -133 -132 -137 -17 63 -69 -54 58 -74 -80 81 0 284 86 192 356 53 52 50 187 132 133 134 135 221 437 448 442 157 159 269 439 566 0\n650 79 -61 -134 -133 -132 -137 -139 -17 63 -69 -54 58 -74 -80 81 0 52 50 649 452 60 107 437 0\n651 63 -69 -54 140 58 68 -80 46 171 0 604 603 502 531 527 512 369 192 190 187 183 607 608 523 371 532 506 505 318 89 456 481 488 485 495 492 499 478 473 475 459 460 467 469 463 444 86 650 181 452 64 217 442 0\n652 -76 -48 -10 -57 -21 -79 -61 -63 -69 -54 -74 -80 0 230 61 181 192 356 231 558 0\n653 47 -57 -21 -79 -61 -133 -137 35 -63 -69 -54 -74 -80 0 62 61 101 95 192 356 267 439 652 312 448 562 0\n654 -79 -61 -133 -137 -139 35 -63 -69 -54 68 -74 -80 81 0 192 356 52 50 181 352 452 58 230 653 159 226 268 448 560 0\n655 -57 79 -132 -54 0 52 50 60 107 437 0\n656 -69 -54 140 58 68 -80 46 171 0 604 603 502 53 52 50 531 527 512 369 192 190 189 187 183 607 608 523 371 528 509 513 117 124 356 651 95 97 98 101 235 456 481 488 485 495 492 499 478 473 475 459 460 469 463 444 654 284 655 452 132 133 134 135 288 437 448 159 269 439 567 0\n657 83 -179 0 554 502 550 531 528 509 508 527 512 342 359 300 627 182 183 184 186 187 189 190 192 369 635 636 637 454 648 656 642 101 324 456 335 481 446 488 464 495 469 499 475 0\n658 -76 -48 -51 -29 -79 -57 71 -68 -54 -14 -63 -23 -179 0 554 230 61 550 531 527 513 657 373 231 583 0\n659 -29 -79 -57 71 -68 -54 -141 -137 -133 -14 -63 -23 -179 0 554 62 61 657 203 201 550 531 527 513 95 294 235 101 96 373 164 456 40 439 658 312 448 595 0\n660 47 -70 -22 51 -77 -79 -57 -68 -54 -133 -14 -63 -23 -179 0 554 62 61 657 203 101 201 550 531 527 513 95 294 233 235 295 373 195 512 232 439 594 0\n661 -54 -141 -137 -139 -133 -132 -135 -14 -63 -23 69 -179 0 554 95 550 531 527 513 657 373 204 202 528 508 50 51 52 444 620 452 58 230 655 659 324 355 313 357 448 660 226 589 0\n662 140 -63 69 58 53 -179 0 554 502 101 98 96 95 550 607 608 523 371 657 363 531 527 513 373 204 203 202 201 199 197 196 528 509 508 455 483 306 490 295 294 497 446 235 498 464 474 469 468 475 472 462 499 459 460 495 493 488 486 478 479 481 661 450 33 41 266 618 168 173 444 448 113 116 128 129 135 225 439 452 32 280 437 556 0\n663 -63 69 58 53 -179 0 554 502 550 531 527 513 657 373 203 201 196 195 96 101 662 454 10 34 59 165 224 446 456 452 464 484 486 469 495 475 499 0\n664 -33 63 69 58 -179 0 554 502 550 531 527 513 657 373 203 201 3 10 54 57 59 224 446 442 452 464 487 466 497 474 498 0\n665 -145 77 63 69 58 -179 0 554 657 196 195 664 454 204 203 202 201 199 550 463 464 446 11 22 35 444 631 0\n666 -57 -134 33 63 58 -179 0 554 657 550 531 528 509 508 64 65 306 442 212 0\n667 77 63 69 58 -179 0 554 502 657 196 195 664 454 483 490 497 498 474 468 550 531 527 513 373 204 203 202 201 665 469 466 475 472 499 459 460 495 493 488 486 478 481 666 452 133 134 135 448 157 158 159 160 243 439 456 446 32 39 462 620 444 0\n668 69 58 53 -179 0 502 657 203 201 196 195 663 664 454 483 490 497 498 474 667 166 173 446 464 469 466 475 666 499 495 493 486 478 452 448 135 0\n669 33 145 63 51 58 -179 0 502 469 475 499 495 488 657 196 195 454 483 481 490 486 497 493 498 478 474 466 666 452 135 448 158 160 173 456 0\n670 145 63 51 18 58 -179 0 554 502 550 531 527 513 657 373 203 469 475 499 495 669 9 59 165 224 291 452 89 486 456 484 0\n671 -33 63 51 18 58 -179 0 554 502 550 531 527 513 657 373 203 3 9 54 57 59 165 224 291 442 452 89 467 456 475 484 499 486 495 0\n672 -37 -137 63 0 8 91 158 309 448 0\n673 47 -19 -79 -56 -15 -70 -77 -17 -68 -133 -54 -69 -179 0 554 129 128 550 531 527 513 657 373 241 163 89 267 439 569 0\n674 57 71 63 58 53 -179 0 554 603 502 657 196 195 668 117 121 671 454 483 670 463 120 550 531 527 513 373 204 202 199 197 532 506 505 452 486 495 492 499 478 479 473 475 450 459 460 467 50 51 52 444 116 672 318 631 89 173 448 126 127 130 225 309 442 437 245 338 673 226 570 0\n675 -47 -15 -70 -68 -77 -79 -17 -54 -14 -57 -69 -179 0 554 126 52 63 58 550 531 527 513 657 373 226 585 0\n676 -57 63 58 53 -179 0 554 502 657 196 195 668 117 121 671 454 483 490 497 498 670 463 120 118 550 531 527 513 373 204 203 202 199 197 528 509 508 511 532 506 505 61 62 65 666 306 467 475 472 499 459 460 495 493 488 478 479 481 672 450 318 610 51 655 456 444 163 173 241 448 309 675 267 439 590 0\n677 -77 -71 156 -135 50 53 -83 0 603 502 135 491 204 202 199 197 168 173 444 448 477 478 450 493 52 499 620 473 459 0\n678 137 -71 156 -135 50 53 -83 0 603 502 491 204 202 199 197 477 478 450 493 51 52 499 444 620 473 459 0\n679 63 58 53 -179 0 554 603 668 121 120 117 657 204 202 199 197 196 195 550 670 463 671 454 483 490 676 674 135 677 678 672 448 160 456 481 488 492 479 450 51 444 631 0\n680 -71 49 -68 141 -179 0 554 502 550 531 527 513 657 373 196 195 224 620 454 459 481 473 488 499 495 0\n681 -48 -33 4 3 38 0 26 27 205 0\n682 36 -133 -33 47 4 35 3 38 0 681 205 439 16 0\n683 49 57 -68 141 47 4 35 3 -179 0 604 502 116 113 111 484 657 199 197 196 195 680 452 485 486 481 495 454 499 4 473 459 460 437 180 682 6 17 207 0\n684 -49 -76 4 -63 -69 53 -83 0 173 96 94 121 201 199 197 196 195 30 31 32 52 261 644 227 454 205 0\n685 -68 -76 58 53 -179 0 554 502 657 668 679 203 101 201 550 531 527 513 117 95 233 684 121 96 173 456 313 607 608 523 371 120 269 161 159 235 94 118 373 202 199 196 195 528 509 511 113 116 683 59 60 61 62 286 454 292 644 481 488 495 499 473 459 460 437 439 580 0\n686 140 68 77 -63 -69 53 -83 0 502 121 96 101 456 204 202 201 199 644 481 51 488 444 495 463 499 469 475 0\n687 -76 58 53 -179 0 554 502 679 101 96 668 121 550 531 527 513 657 373 204 202 196 195 173 456 484 685 686 454 21 59 224 444 452 463 486 469 495 475 499 0\n688 -33 76 62 37 51 -73 0 603 59 165 223 224 456 448 452 484 478 486 492 0\n689 47 -79 -133 -70 -57 -68 -54 -26 -29 -14 -63 -69 -179 0 554 62 61 657 203 201 550 531 527 513 117 95 235 101 373 267 439 591 0\n690 77 58 53 -179 0 554 604 603 502 657 203 202 550 531 527 511 679 668 117 118 513 373 121 96 101 687 688 292 196 195 454 201 95 233 235 199 528 508 324 456 237 644 686 618 50 52 116 488 485 680 495 492 452 499 478 58 60 230 473 448 459 460 437 689 226 586 0\n691 -47 -54 -68 -70 -57 -77 -14 -63 -69 -179 0 554 503 443 447 445 465 470 457 482 453 489 449 451 480 496 501 476 52 230 63 58 550 531 527 513 657 373 226 440 461 438 336 351 565 0\n692 -133 -54 -68 -70 -57 -77 -14 -63 -69 -179 0 554 503 101 95 691 267 443 447 445 465 470 457 482 453 489 449 451 480 496 501 476 62 61 657 203 201 550 531 527 513 117 235 373 461 439 438 336 351 564 0\n693 -54 -68 -70 -57 -77 -142 -14 -63 -69 -179 0 554 107 63 60 101 95 550 531 527 513 657 373 52 691 267 692 441 458 263 260 437 584 0\n694 47 -133 -132 54 -68 -70 -57 -77 -14 -63 -69 -179 0 554 550 531 527 513 657 199 197 270 252 107 63 62 61 60 203 201 117 95 235 101 373 267 439 32 250 557 437 0\n695 79 -47 -132 -11 -68 -70 -57 -77 -14 -63 -69 -179 0 554 107 63 60 550 531 527 513 657 373 336 351 437 563 0\n696 -68 -70 -57 58 53 -179 0 554 502 61 690 657 196 195 550 531 527 513 373 668 121 679 96 101 687 688 454 483 490 497 498 471 203 202 511 117 118 292 120 199 197 693 450 270 479 493 499 473 459 460 694 28 695 285 555 264 0\n697 -47 -79 -21 -54 -20 -70 -57 -77 -14 -63 -69 -179 0 554 52 230 63 58 550 531 527 513 657 373 226 559 0\n698 -70 -57 58 53 -179 0 554 502 107 62 61 690 168 657 196 195 550 531 527 513 373 668 121 679 96 101 687 688 454 483 490 497 498 203 202 511 117 118 292 201 95 235 120 204 199 197 696 444 347 463 469 475 472 499 459 460 493 479 450 278 655 697 267 439 561 0\n699 47 -68 -79 -133 -54 -24 -25 -57 -77 -14 -63 -69 -179 0 554 62 61 657 203 201 550 531 527 513 117 95 235 101 373 267 439 575 0\n700 -57 58 53 -179 0 554 603 502 690 168 657 196 195 550 531 527 513 373 668 121 679 96 101 687 688 454 483 490 491 203 202 511 117 118 292 120 204 199 197 528 509 58 63 230 698 448 308 286 478 477 493 450 499 52 473 475 459 460 469 655 463 444 699 226 572 0\n701 151 57 -77 153 50 53 -83 0 603 502 490 492 493 486 499 452 475 677 469 463 0\n702 -47 -19 -79 -68 -13 -54 -70 -77 -14 -63 -69 -179 0 554 245 52 50 126 550 531 527 513 657 373 226 571 0\n703 58 53 -179 0 554 502 550 531 527 513 657 373 204 203 202 201 199 197 196 195 511 668 117 118 120 121 679 95 96 98 101 235 687 688 454 292 483 690 168 700 701 478 479 448 450 128 129 135 225 287 50 52 452 486 495 499 473 475 459 460 469 463 444 116 437 338 702 267 439 568 0\n704 47 -54 -57 -77 -58 -179 0 554 502 657 196 195 68 454 483 490 131 173 448 478 493 499 473 459 655 550 531 528 509 286 61 201 203 70 475 469 464 446 202 204 168 463 444 460 527 513 373 241 163 99 93 74 72 532 506 267 439 256 259 574 0\n705 -77 53 -179 0 554 603 502 657 196 195 703 68 454 483 490 491 131 99 74 70 550 531 527 513 373 204 203 202 201 199 197 528 509 532 506 168 173 448 478 477 493 499 473 475 459 469 463 464 444 446 120 701 450 60 61 286 655 252 704 28 255 258 573 251 0\n706 -69 53 -179 0 554 603 502 703 66 70 657 705 331 196 195 68 454 131 99 93 74 72 69 550 531 527 513 373 204 202 199 197 607 608 523 371 528 509 120 121 456 481 488 495 492 499 478 479 473 475 448 450 459 460 469 156 157 159 239 269 310 51 52 463 444 683 61 286 655 576 439 0\n707 53 -179 0 554 502 550 531 527 513 657 373 204 203 202 201 199 197 196 195 607 608 523 371 528 509 703 66 68 69 70 72 74 93 99 131 454 483 490 497 498 474 468 705 331 706 363 446 464 462 469 475 472 499 459 460 495 493 488 486 478 479 481 448 456 157 159 310 39 41 444 450 52 620 452 61 286 655 439 579 0\n708 17 82 69 37 43 51 52 58 22 65 63 72 77 81 0 599 322 0\n709 -179 0 554 502 550 531 532 528 505 506 508 509 607 608 523 371 657 195 196 201 203 707 44 45 46 47 122 169 454 446 464 469 475 499 495 488 481 456 89 93 101 316 708 0\n710 -177 0 709 543 0\n711 -175 0 709 547 0\n712 171 0 709 553 548 0\n713 -167 0 710 608 0\n714 -52 0 713 523 0\n715 -81 0 714 371 0\n716 -83 -144 -164 60 64 -29 69 0 198 200 202 204 333 510 446 79 115 462 444 0\n717 -67 33 64 0 715 344 361 615 0\n718 -61 -164 0 84 85 88 510 0\n719 -39 -164 0 15 20 78 510 0\n720 72 -29 37 51 82 63 69 58 77 0 715 712 502 354 102 375 366 507 322 504 81 89 530 456 526 484 490 497 498 474 468 716 342 300 717 718 719 446 464 462 469 444 475 112 115 499 495 488 481 454 12 19 510 0\n721 -29 37 51 82 63 69 58 77 0 554 715 714 354 102 720 136 138 139 141 155 178 191 367 508 717 343 505 528 533 551 544 535 521 341 358 345 600 0\n722 -72 29 37 51 63 69 77 0 502 137 143 151 162 178 325 330 448 329 89 478 446 456 464 484 469 490 475 493 499 0\n723 37 51 82 63 69 58 77 0 715 714 375 721 353 722 366 321 708 0\n724 -37 82 63 0 375 8 24 55 91 158 254 309 253 256 307 597 0\n725 82 63 69 58 77 0 712 502 375 724 723 34 35 36 37 38 39 103 140 147 152 504 717 507 304 303 530 526 446 510 75 76 115 454 444 483 462 490 468 497 474 498 0\n726 -82 69 0 606 554 715 714 376 509 106 506 528 534 533 529 551 511 544 535 537 519 520 521 517 361 360 342 359 341 358 345 600 0\n727 -72 -63 69 77 0 715 101 95 140 162 367 326 25 319 311 265 266 598 0\n728 51 69 58 77 0 712 714 502 726 725 727 507 375 366 504 530 526 719 718 324 101 100 98 96 317 456 102 484 446 490 464 497 469 498 475 474 499 468 495 462 716 488 342 300 481 717 444 112 618 454 297 19 0\n729 69 58 77 0 712 502 726 375 725 100 727 366 507 504 530 526 718 719 728 34 36 38 39 103 717 510 446 75 76 115 454 444 483 462 490 468 497 474 498 0\n730 -32 -164 45 0 13 76 510 0\n731 -33 -164 45 0 14 77 510 0\n732 40 -139 -164 -63 82 -69 0 119 731 718 98 97 124 118 117 292 510 211 216 288 452 0\n733 -63 82 -69 77 0 712 604 603 375 356 124 123 122 121 120 119 117 95 96 101 320 326 234 236 456 504 507 530 526 730 731 454 481 488 485 492 479 732 18 49 450 0\n734 -40 -17 72 -164 82 -69 58 0 366 119 731 718 375 125 123 23 145 185 198 296 339 340 293 346 596 0\n735 72 -164 82 58 77 0 715 604 729 119 731 730 718 733 724 356 124 122 121 120 118 117 322 89 456 734 510 75 80 150 154 271 272 454 290 276 481 208 213 216 485 220 452 0\n736 -164 82 77 58 0 606 735 367 508 505 529 534 0\n737 -83 59 0 711 521 373 539 515 0\n738 -78 40 0 711 365 519 517 539 0\n739 164 -29 -69 0 711 124 123 118 117 511 513 737 738 328 362 516 520 539 0\n740 -164 58 77 0 606 736 376 509 506 529 534 0\n741 58 77 0 729 356 739 740 0\n742 -69 77 0 712 715 604 741 193 142 507 105 73 504 530 526 71 738 364 93 69 68 67 119 120 121 122 730 510 456 75 150 271 272 209 219 454 276 220 481 452 485 0\n743 74 77 0 502 741 70 82 104 742 446 464 469 475 499 495 71 738 364 323 142 68 67 66 328 195 196 737 454 209 219 374 483 220 486 452 0\n744 77 0 715 712 741 68 69 70 71 73 82 104 105 142 193 717 738 504 507 274 530 526 743 144 146 147 149 150 636 510 298 0\n745 -16 0 744 163 0\n746 -33 0 744 165 0\n747 -39 0 744 166 0\n748 -40 0 744 167 0\n749 -46 0 744 168 0\n750 -53 0 744 169 0\n751 -62 0 744 170 0\n752 -74 0 744 171 0\n753 -75 0 744 172 0\n754 -76 0 744 173 0\n755 -78 0 744 179 0\n756 -80 0 744 192 0\n757 -67 0 753 344 0\n758 -61 0 756 343 0\n759 -64 0 756 715 360 0\n760 -58 0 752 753 759 745 751 754 746 756 755 750 744 66 131 302 234 448 196 737 478 454 219 374 483 275 701 0\n761 -59 0 746 757 758 749 502 754 747 759 760 748 75 76 80 83 115 513 454 444 483 463 490 469 497 475 498 499 474 495 493 468 466 486 478 462 448 446 127 130 194 442 732 0\n762 -83 0 761 737 0\n763 -69 0 762 755 756 362 0\n764 -20 0 762 753 756 341 0\n765 -68 0 762 753 756 345 0\n766 -23 0 762 756 715 755 358 0\n767 0 764 763 762 757 766 748 714 750 758 759 749 753 755 756 715 765 600 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.l) :=
(.branch 20
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
 (.leaf (⟨10, by decide⟩))
 (.leaf (⟨11, by decide⟩)))
 (.branch 13
 (.leaf (⟨12, by decide⟩))
 (.branch 14
 (.leaf (⟨13, by decide⟩))
 (.leaf (⟨14, by decide⟩)))))
 (.branch 17
 (.branch 16
 (.leaf (⟨15, by decide⟩))
 (.leaf (⟨16, by decide⟩)))
 (.branch 18
 (.leaf (⟨17, by decide⟩))
 (.branch 19
 (.leaf (⟨18, by decide⟩))
 (.leaf (⟨19, by decide⟩)))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (⟨20, by decide⟩))
 (.leaf (⟨21, by decide⟩)))
 (.branch 23
 (.leaf (⟨22, by decide⟩))
 (.branch 24
 (.leaf (⟨23, by decide⟩))
 (.leaf (⟨24, by decide⟩)))))
 (.branch 27
 (.branch 26
 (.leaf (⟨25, by decide⟩))
 (.leaf (⟨26, by decide⟩)))
 (.branch 28
 (.leaf (⟨27, by decide⟩))
 (.branch 29
 (.leaf (⟨28, by decide⟩))
 (.leaf (⟨29, by decide⟩))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (⟨30, by decide⟩))
 (.leaf (⟨31, by decide⟩)))
 (.branch 33
 (.leaf (⟨32, by decide⟩))
 (.branch 34
 (.leaf (⟨33, by decide⟩))
 (.leaf (⟨34, by decide⟩)))))
 (.branch 38
 (.branch 36
 (.leaf (⟨35, by decide⟩))
 (.branch 37
 (.leaf (⟨36, by decide⟩))
 (.leaf (⟨37, by decide⟩))))
 (.branch 39
 (.leaf (⟨38, by decide⟩))
 (.branch 40
 (.leaf (⟨39, by decide⟩))
 (.leaf (⟨40, by decide⟩))))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.g)) :=
(.branch 20
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
 (.leaf ([]))
 (.leaf ([])))
 (.branch 13
 (.leaf ([]))
 (.branch 14
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 17
 (.branch 16
 (.leaf ([]))
 (.leaf ([])))
 (.branch 18
 (.leaf ([]))
 (.branch 19
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ([]))
 (.leaf ([])))
 (.branch 23
 (.leaf ([]))
 (.branch 24
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 27
 (.branch 26
 (.leaf ([]))
 (.leaf ([])))
 (.branch 28
 (.leaf ([]))
 (.branch 29
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ([]))
 (.leaf ([])))
 (.branch 33
 (.leaf ([]))
 (.branch 34
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 38
 (.branch 36
 (.leaf ([]))
 (.branch 37
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 39
 (.leaf ([]))
 (.branch 40
 (.leaf ([]))
 (.leaf ([]))))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record043

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record036
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "15c4f1e274aaa6a95a4eac6a98e68ba1e1783e785d1e26a96a5594e6c5a9565395554d54d8b52d8751d1743db0dc3a8da358ce364d5334d33a2d8b52e2b4acab86d1b16c3ba1e4731e2729c6785c3713c568382e079c1685514a5191560d0b41da0cc328c5382c2b06e0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6d24926d24db69b49249249a6934da492492492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 62), (facetIndex 68), (facetIndex 72)]))
 (.leaf ([(facetIndex 39), (facetIndex 58), (facetIndex 67), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 45), (facetIndex 53)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 59)]))
 (.leaf ([(facetIndex 48), (facetIndex 50), (facetIndex 52), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 40)]))
 (.branch 8
 (.leaf ([(facetIndex 30), (facetIndex 38), (facetIndex 43), (facetIndex 51)]))
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 28), (facetIndex 29), (facetIndex 33)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "22225000101000000041444435750500307006176666833788882z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 42), (facetIndex 70), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 60), (facetIndex 61), (facetIndex 64)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 41), (facetIndex 44), (facetIndex 47), (facetIndex 49), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 84)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49b7bb248000024000301b000000028a05068z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6, 7, 8]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [4, 5, 6, 7]
def grouped3_0018 : List Nat := [5]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7]
def grouped3_0021 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record036" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record036" 68

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record036" "{\"ridges\":[[11,641],[17,296],[18,321],[19,416],[20,448],[33,641],[39,296],[41,330],[43,642],[46,321],[48,194],[49,354],[50,416],[51,642],[52,448],[53,641],[56,280],[58,296],[61,308],[62,336],[64,356],[67,296],[68,336],[69,296],[71,904],[72,448],[73,416],[73,448],[81,306],[84,680],[86,354],[88,332]],\"owners\":[[48,194,[80,85],[10,31,45,52,53,78,86]],[11,641,[65,66,70,71],[33,43,51,53]],[33,641,[70,71],[11,43,51,53,65,66]],[53,641,[65,70,71],[11,33,43,51,66]],[43,642,[79,80],[11,33,51,53,84]],[51,642,[80],[11,33,43,53,79,84]],[56,280,[81,82],[16,36,67,68,87,88]],[17,296,[81,83,87],[39,58,67,69]],[39,296,[87],[17,58,67,69,81,83]],[58,296,[81,83],[17,39,67,69,87]],[67,296,[83],[17,39,58,69,81,87]],[69,296,[81,87],[17,39,58,67,83]],[18,321,[20,41,49,52,60,64,73],[46,62,68]],[46,321,[20,60,64,73],[18,41,49,52,62,68]],[62,336,[82,85],[18,46,68,72,88]],[68,336,[85],[18,46,62,72,82,88]],[19,416,[83,86],[50,69,73]],[50,416,[],[19,69,73,83,86]],[73,416,[83],[19,50,69,86]],[20,448,[85,86],[52,72,73]],[52,448,[],[20,72,73,85,86]],[72,448,[86],[20,52,73,85]],[73,448,[85],[20,52,72,86]],[41,330,[82],[]],[81,306,[44],[]],[49,354,[86],[]],[86,354,[49],[]],[88,332,[60],[]],[61,308,[87],[]],[64,356,[],[]],[84,680,[70],[]],[71,904,[],[]]],\"edges\":[[37,[17,19,39,44,49,50,58,61,64,67,69,73,81,83,86,87]],[40,[18,20,41,46,49,52,60,62,64,68,72,73,82,85,86,88]],[43,[11,33,43,51,53,65,66,70,71,79,80,84]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record036" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record036\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-24,-18],[-24,-19],[-24,-21],[-24,-23],[-12,38,43],[-1,28,29,33,34],[-6,33,34],[-17,28,33,34],[-9,37,38],[-15,38],[-20,39,40],[-2,39,41,45],[-7,45],[-22,39,41],[-30,41],[-32,39,45],[-3,5,8,13,16,24,27,36],[-11,5,24,27,36],[-26,40,43],[-31,43],[-4,41,44],[-14],[-36,41],[-5,43,44],[-16],[-35,44],[-36,43],[-8,40],[-39,10],[-13,44],[-44,13],[-46,24],[-25,45],[-27],[-42,33],[-34],[-47,18,19,20,21,23],[-48,12,14,16,36],[-49,47,48],[-50,49],[-51,50],[51],[-28,52],[-29,52],[-33,53],[-37,54],[-38,54],[-24,55],[-45,56],[-10,57],[-13,57],[-41,57],[-39,58],[-40,58],[-43,58],[-44,58],[-53,59],[-52,59],[-54,60],[-54,-55,61],[-60,62],[-61,63],[-59,62],[-57,64],[-56,64],[-58,65],[-64,66],[-64,-65,67],[-62,-67,68],[-63,-66,68],[-68],[2,4,7,10,13,14,22,25,27,30,32,36,39,41,44,45],[3,5,8,11,13,16,24,26,27,31,35,36,40,43,44,46],[1,6,9,15,17,28,29,33,34,37,38,42]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":57},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"mate\",\"ridge\":194,\"a\":48,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":11,\"owners\":[65,66,70,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":33,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":53,\"owners\":[65,70,71]},{\"tag\":\"mate\",\"ridge\":642,\"a\":43,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":280,\"a\":56,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":296,\"a\":17,\"owners\":[81,83,87]},{\"tag\":\"mate\",\"ridge\":296,\"a\":39,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":296,\"a\":58,\"owners\":[81,83]},{\"tag\":\"mate\",\"ridge\":296,\"a\":67,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":296,\"a\":69,\"owners\":[81,87]},{\"tag\":\"mate\",\"ridge\":321,\"a\":18,\"owners\":[20,41,49,52,60,64,73]},{\"tag\":\"mate\",\"ridge\":321,\"a\":46,\"owners\":[20,60,64,73]},{\"tag\":\"mate\",\"ridge\":336,\"a\":62,\"owners\":[82,85]},{\"tag\":\"mate\",\"ridge\":336,\"a\":68,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":416,\"a\":19,\"owners\":[83,86]},{\"tag\":\"mate\",\"ridge\":416,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":416,\"a\":73,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":448,\"a\":20,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":448,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":448,\"a\":72,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":448,\"a\":73,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":330,\"a\":41,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":306,\"a\":81,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":354,\"a\":49,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":354,\"a\":86,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":332,\"a\":88,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":308,\"a\":61,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":356,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":680,\"a\":84,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":904,\"a\":71,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[54,55,56,57,59],\"full_literals\":[-47,18,19,20,21,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[48,50,52,73],\"full_literals\":[-48,12,14,16,36]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,47,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-50,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-51,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-28,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-29,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-33,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-37,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-38,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":60,\"full_literals\":[-24,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":87,\"full_literals\":[-45,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":44,\"full_literals\":[-10,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":49,\"full_literals\":[-13,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-41,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-39,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-40,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-43,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-44,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-55,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[17,19,39,44,49,50,58,61,64,67,69,73,81,83,86,87]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[18,20,41,46,49,52,60,62,64,68,72,73,82,85,86,88]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[11,33,43,51,53,65,66,70,71,79,80,84]}]}"
  "75 -48 12 36 0 22 25 38 0\n76 50 0 42 41 0\n77 49 0 76 40 0\n78 2 4 7 10 13 22 25 30 32 36 39 41 44 45 0 22 34 72 0\n79 3 5 8 11 13 24 26 31 35 36 40 43 44 46 0 25 34 73 0\n80 1 6 9 15 17 28 29 33 37 38 42 0 36 74 0\n81 62 0 36 61 63 59 57 58 46 47 45 43 44 9 10 7 35 6 8 80 0\n82 -67 0 81 71 69 0\n83 64 0 64 65 50 51 52 49 29 31 15 21 23 13 33 12 14 16 78 0\n84 66 0 83 67 0\n85 -65 0 83 82 68 0\n86 -63 0 84 71 70 0\n87 -58 0 85 66 0\n88 -61 0 86 62 0\n89 -39 0 87 53 0\n90 -40 0 87 54 0\n91 -43 0 87 55 0\n92 -44 0 87 56 0\n93 -20 0 89 90 11 0\n94 -26 0 90 91 19 0\n95 -8 0 90 28 0\n96 -31 0 91 20 0\n97 -5 0 91 92 24 0\n98 -36 0 91 27 0\n99 -35 0 92 26 0\n100 -13 0 92 30 0\n101 24 0 25 34 97 92 91 90 98 99 96 94 100 95 32 17 18 79 0\n102 -18 0 101 1 0\n103 -19 0 101 2 0\n104 -21 0 101 3 0\n105 -23 0 101 4 0\n106 55 0 101 48 0\n107 -47 0 103 102 93 104 105 37 0\n108 -54 0 106 88 60 0\n109 48 0 107 77 39 0\n110 -38 0 108 47 0\n111 12 0 109 98 75 0\n112 0 111 110 91 5 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00053.record036
