module
prelude
public import SixBudgetEnumeration

@[expose] public section

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace Papers.RationalityTen.SixBudgetEnumeration

def literalRows4 : List Row := [
  ⟨10, 14, 7, [0,0,0,0,0,0,4]⟩,
  ⟨10, 14, 8, [0,0,0,0,0,0,4]⟩,
  ⟨10, 14, 9, [0,0,0,0,0,0,4]⟩,
  ⟨11, 14, 8, [0,0,0,0,0,0,4]⟩,
  ⟨11, 14, 9, [0,0,0,0,0,0,4]⟩,
  ⟨12, 14, 9, [0,0,0,0,0,0,4]⟩,
  ⟨10, 14, 7, [0,0,0,0,0,1,3]⟩,
  ⟨10, 14, 8, [0,0,0,0,0,1,3]⟩,
  ⟨11, 14, 8, [0,0,0,0,0,1,3]⟩,
  ⟨10, 14, 7, [0,0,0,0,0,2,2]⟩,
  ⟨10, 14, 4, [0,0,0,0,2,0,2]⟩,
  ⟨10, 14, 5, [0,0,0,0,2,0,2]⟩,
  ⟨11, 14, 5, [0,0,0,0,2,0,2]⟩,
  ⟨10, 14, 4, [0,0,0,0,2,1,1]⟩,
  ⟨10, 14, 1, [0,0,0,0,4,0,0]⟩,
  ⟨10, 14, 7, [0,0,0,1,0,0,3]⟩,
  ⟨10, 14, 8, [0,0,0,1,0,0,3]⟩,
  ⟨11, 14, 8, [0,0,0,1,0,0,3]⟩,
  ⟨10, 14, 7, [0,0,0,1,0,1,2]⟩,
  ⟨10, 14, 4, [0,0,0,1,2,0,1]⟩,
  ⟨10, 14, 7, [0,0,0,2,0,0,2]⟩,
  ⟨10, 14, 7, [0,0,1,0,0,0,3]⟩,
  ⟨10, 14, 7, [0,0,1,0,0,1,2]⟩,
  ⟨10, 14, 4, [0,0,1,0,2,0,1]⟩,
  ⟨10, 14, 7, [0,1,0,0,0,0,3]⟩,
  ⟨10, 14, 8, [0,1,0,0,0,0,3]⟩,
  ⟨11, 14, 8, [0,1,0,0,0,0,3]⟩,
  ⟨10, 14, 7, [0,1,0,0,0,1,2]⟩,
  ⟨10, 14, 4, [0,1,0,0,2,0,1]⟩,
  ⟨10, 14, 7, [0,1,0,1,0,0,2]⟩,
  ⟨10, 14, 7, [0,2,0,0,0,0,2]⟩,
  ⟨10, 14, 7, [1,0,0,0,0,0,3]⟩,
  ⟨10, 14, 7, [1,0,0,0,0,1,2]⟩,
  ⟨10, 14, 4, [1,0,0,0,2,0,1]⟩
]

theorem typeLists4_eq : typeLists 4 =
  [[0,0,0,0,0,0,4], [0,0,0,0,0,1,3], [0,0,0,0,0,2,2], [0,0,0,0,0,3,1], [0,0,0,0,0,4,0], [0,0,0,0,2,0,2], [0,0,0,0,2,1,1], [0,0,0,0,2,2,0], [0,0,0,0,4,0,0], [0,0,0,1,0,0,3], [0,0,0,1,0,1,2], [0,0,0,1,0,2,1], [0,0,0,1,2,0,1], [0,0,0,1,2,1,0], [0,0,0,2,0,0,2], [0,0,0,2,2,0,0], [0,0,1,0,0,0,3], [0,0,1,0,0,1,2], [0,0,1,0,2,0,1], [0,0,1,0,2,1,0], [0,1,0,0,0,0,3], [0,1,0,0,0,1,2], [0,1,0,0,0,2,1], [0,1,0,0,2,0,1], [0,1,0,0,2,1,0], [0,1,0,1,0,0,2], [0,1,0,1,2,0,0], [0,2,0,0,0,0,2], [0,2,0,0,2,0,0], [1,0,0,0,0,0,3], [1,0,0,0,0,1,2], [1,0,0,0,2,0,1], [1,0,0,0,2,1,0]] := by decide +kernel

theorem rowsForTypes4_000_eq : rowsForTypes 4 [0,0,0,0,0,0,4] =
[
  ⟨10, 14, 7, [0,0,0,0,0,0,4]⟩,
  ⟨10, 14, 8, [0,0,0,0,0,0,4]⟩,
  ⟨10, 14, 9, [0,0,0,0,0,0,4]⟩,
  ⟨11, 14, 8, [0,0,0,0,0,0,4]⟩,
  ⟨11, 14, 9, [0,0,0,0,0,0,4]⟩,
  ⟨12, 14, 9, [0,0,0,0,0,0,4]⟩
] := by decide +kernel

theorem rowsForTypes4_001_eq : rowsForTypes 4 [0,0,0,0,0,1,3] =
[
  ⟨10, 14, 7, [0,0,0,0,0,1,3]⟩,
  ⟨10, 14, 8, [0,0,0,0,0,1,3]⟩,
  ⟨11, 14, 8, [0,0,0,0,0,1,3]⟩
] := by decide +kernel

theorem rowsForTypes4_002_eq : rowsForTypes 4 [0,0,0,0,0,2,2] =
[
  ⟨10, 14, 7, [0,0,0,0,0,2,2]⟩
] := by decide +kernel

theorem rowsForTypes4_003_eq : rowsForTypes 4 [0,0,0,0,0,3,1] =
[

] := by decide +kernel

theorem rowsForTypes4_004_eq : rowsForTypes 4 [0,0,0,0,0,4,0] =
[

] := by decide +kernel

theorem rowsForTypes4_005_eq : rowsForTypes 4 [0,0,0,0,2,0,2] =
[
  ⟨10, 14, 4, [0,0,0,0,2,0,2]⟩,
  ⟨10, 14, 5, [0,0,0,0,2,0,2]⟩,
  ⟨11, 14, 5, [0,0,0,0,2,0,2]⟩
] := by decide +kernel

theorem rowsForTypes4_006_eq : rowsForTypes 4 [0,0,0,0,2,1,1] =
[
  ⟨10, 14, 4, [0,0,0,0,2,1,1]⟩
] := by decide +kernel

theorem rowsForTypes4_007_eq : rowsForTypes 4 [0,0,0,0,2,2,0] =
[

] := by decide +kernel

theorem rowsForTypes4_008_eq : rowsForTypes 4 [0,0,0,0,4,0,0] =
[
  ⟨10, 14, 1, [0,0,0,0,4,0,0]⟩
] := by decide +kernel

theorem rowsForTypes4_009_eq : rowsForTypes 4 [0,0,0,1,0,0,3] =
[
  ⟨10, 14, 7, [0,0,0,1,0,0,3]⟩,
  ⟨10, 14, 8, [0,0,0,1,0,0,3]⟩,
  ⟨11, 14, 8, [0,0,0,1,0,0,3]⟩
] := by decide +kernel

theorem rowsForTypes4_010_eq : rowsForTypes 4 [0,0,0,1,0,1,2] =
[
  ⟨10, 14, 7, [0,0,0,1,0,1,2]⟩
] := by decide +kernel

theorem rowsForTypes4_011_eq : rowsForTypes 4 [0,0,0,1,0,2,1] =
[

] := by decide +kernel

theorem rowsForTypes4_012_eq : rowsForTypes 4 [0,0,0,1,2,0,1] =
[
  ⟨10, 14, 4, [0,0,0,1,2,0,1]⟩
] := by decide +kernel

theorem rowsForTypes4_013_eq : rowsForTypes 4 [0,0,0,1,2,1,0] =
[

] := by decide +kernel

theorem rowsForTypes4_014_eq : rowsForTypes 4 [0,0,0,2,0,0,2] =
[
  ⟨10, 14, 7, [0,0,0,2,0,0,2]⟩
] := by decide +kernel

theorem rowsForTypes4_015_eq : rowsForTypes 4 [0,0,0,2,2,0,0] =
[

] := by decide +kernel

theorem rowsForTypes4_016_eq : rowsForTypes 4 [0,0,1,0,0,0,3] =
[
  ⟨10, 14, 7, [0,0,1,0,0,0,3]⟩
] := by decide +kernel

theorem rowsForTypes4_017_eq : rowsForTypes 4 [0,0,1,0,0,1,2] =
[
  ⟨10, 14, 7, [0,0,1,0,0,1,2]⟩
] := by decide +kernel

theorem rowsForTypes4_018_eq : rowsForTypes 4 [0,0,1,0,2,0,1] =
[
  ⟨10, 14, 4, [0,0,1,0,2,0,1]⟩
] := by decide +kernel

theorem rowsForTypes4_019_eq : rowsForTypes 4 [0,0,1,0,2,1,0] =
[

] := by decide +kernel

theorem rowsForTypes4_020_eq : rowsForTypes 4 [0,1,0,0,0,0,3] =
[
  ⟨10, 14, 7, [0,1,0,0,0,0,3]⟩,
  ⟨10, 14, 8, [0,1,0,0,0,0,3]⟩,
  ⟨11, 14, 8, [0,1,0,0,0,0,3]⟩
] := by decide +kernel

theorem rowsForTypes4_021_eq : rowsForTypes 4 [0,1,0,0,0,1,2] =
[
  ⟨10, 14, 7, [0,1,0,0,0,1,2]⟩
] := by decide +kernel

theorem rowsForTypes4_022_eq : rowsForTypes 4 [0,1,0,0,0,2,1] =
[

] := by decide +kernel

theorem rowsForTypes4_023_eq : rowsForTypes 4 [0,1,0,0,2,0,1] =
[
  ⟨10, 14, 4, [0,1,0,0,2,0,1]⟩
] := by decide +kernel

theorem rowsForTypes4_024_eq : rowsForTypes 4 [0,1,0,0,2,1,0] =
[

] := by decide +kernel

theorem rowsForTypes4_025_eq : rowsForTypes 4 [0,1,0,1,0,0,2] =
[
  ⟨10, 14, 7, [0,1,0,1,0,0,2]⟩
] := by decide +kernel

theorem rowsForTypes4_026_eq : rowsForTypes 4 [0,1,0,1,2,0,0] =
[

] := by decide +kernel

theorem rowsForTypes4_027_eq : rowsForTypes 4 [0,2,0,0,0,0,2] =
[
  ⟨10, 14, 7, [0,2,0,0,0,0,2]⟩
] := by decide +kernel

theorem rowsForTypes4_028_eq : rowsForTypes 4 [0,2,0,0,2,0,0] =
[

] := by decide +kernel

theorem rowsForTypes4_029_eq : rowsForTypes 4 [1,0,0,0,0,0,3] =
[
  ⟨10, 14, 7, [1,0,0,0,0,0,3]⟩
] := by decide +kernel

theorem rowsForTypes4_030_eq : rowsForTypes 4 [1,0,0,0,0,1,2] =
[
  ⟨10, 14, 7, [1,0,0,0,0,1,2]⟩
] := by decide +kernel

theorem rowsForTypes4_031_eq : rowsForTypes 4 [1,0,0,0,2,0,1] =
[
  ⟨10, 14, 4, [1,0,0,0,2,0,1]⟩
] := by decide +kernel

theorem rowsForTypes4_032_eq : rowsForTypes 4 [1,0,0,0,2,1,0] =
[

] := by decide +kernel

theorem rowsForTotal4_eq : rowsForTotal 4 = literalRows4 := by
  simp only [rowsForTotal, typeLists4_eq, List.flatMap_cons, List.flatMap_nil, rowsForTypes4_000_eq, rowsForTypes4_001_eq, rowsForTypes4_002_eq, rowsForTypes4_003_eq, rowsForTypes4_004_eq, rowsForTypes4_005_eq, rowsForTypes4_006_eq, rowsForTypes4_007_eq, rowsForTypes4_008_eq, rowsForTypes4_009_eq, rowsForTypes4_010_eq, rowsForTypes4_011_eq, rowsForTypes4_012_eq, rowsForTypes4_013_eq, rowsForTypes4_014_eq, rowsForTypes4_015_eq, rowsForTypes4_016_eq, rowsForTypes4_017_eq, rowsForTypes4_018_eq, rowsForTypes4_019_eq, rowsForTypes4_020_eq, rowsForTypes4_021_eq, rowsForTypes4_022_eq, rowsForTypes4_023_eq, rowsForTypes4_024_eq, rowsForTypes4_025_eq, rowsForTypes4_026_eq, rowsForTypes4_027_eq, rowsForTypes4_028_eq, rowsForTypes4_029_eq, rowsForTypes4_030_eq, rowsForTypes4_031_eq, rowsForTypes4_032_eq]
  rfl

#print axioms rowsForTotal4_eq

end Papers.RationalityTen.SixBudgetEnumeration
