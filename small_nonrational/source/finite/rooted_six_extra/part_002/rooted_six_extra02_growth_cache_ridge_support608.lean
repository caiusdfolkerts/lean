module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport608Part000
public import RootedSixExtra02GrowthCacheRidgeSupport608Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport608_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport608_rest_010 =
    (ridgeSupport608_suffix_010, ridgeSupport608_rest_010) := by rfl
theorem ridgeSupport608_suffix_decode_009 : PackedRawNatGrowth.readList 13 11 ridgeSupport608_rest_009 =
    (ridgeSupport608_suffix_009, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 11 0
    ridgeSupport608_rest_009 ridgeSupport608_rest_010 ridgeSupport608_rest_010
    ridgeSupport608_009 ridgeSupport608_suffix_010 ridgeSupport608_009_decode ridgeSupport608_suffix_decode_010
theorem ridgeSupport608_suffix_decode_008 : PackedRawNatGrowth.readList 13 43 ridgeSupport608_rest_008 =
    (ridgeSupport608_suffix_008, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 11
    ridgeSupport608_rest_008 ridgeSupport608_rest_009 ridgeSupport608_rest_010
    ridgeSupport608_008 ridgeSupport608_suffix_009 ridgeSupport608_008_decode ridgeSupport608_suffix_decode_009
theorem ridgeSupport608_suffix_decode_007 : PackedRawNatGrowth.readList 13 75 ridgeSupport608_rest_007 =
    (ridgeSupport608_suffix_007, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 43
    ridgeSupport608_rest_007 ridgeSupport608_rest_008 ridgeSupport608_rest_010
    ridgeSupport608_007 ridgeSupport608_suffix_008 ridgeSupport608_007_decode ridgeSupport608_suffix_decode_008
theorem ridgeSupport608_suffix_decode_006 : PackedRawNatGrowth.readList 13 107 ridgeSupport608_rest_006 =
    (ridgeSupport608_suffix_006, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 75
    ridgeSupport608_rest_006 ridgeSupport608_rest_007 ridgeSupport608_rest_010
    ridgeSupport608_006 ridgeSupport608_suffix_007 ridgeSupport608_006_decode ridgeSupport608_suffix_decode_007
theorem ridgeSupport608_suffix_decode_005 : PackedRawNatGrowth.readList 13 139 ridgeSupport608_rest_005 =
    (ridgeSupport608_suffix_005, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 107
    ridgeSupport608_rest_005 ridgeSupport608_rest_006 ridgeSupport608_rest_010
    ridgeSupport608_005 ridgeSupport608_suffix_006 ridgeSupport608_005_decode ridgeSupport608_suffix_decode_006
theorem ridgeSupport608_suffix_decode_004 : PackedRawNatGrowth.readList 13 171 ridgeSupport608_rest_004 =
    (ridgeSupport608_suffix_004, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 139
    ridgeSupport608_rest_004 ridgeSupport608_rest_005 ridgeSupport608_rest_010
    ridgeSupport608_004 ridgeSupport608_suffix_005 ridgeSupport608_004_decode ridgeSupport608_suffix_decode_005
theorem ridgeSupport608_suffix_decode_003 : PackedRawNatGrowth.readList 13 203 ridgeSupport608_rest_003 =
    (ridgeSupport608_suffix_003, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 171
    ridgeSupport608_rest_003 ridgeSupport608_rest_004 ridgeSupport608_rest_010
    ridgeSupport608_003 ridgeSupport608_suffix_004 ridgeSupport608_003_decode ridgeSupport608_suffix_decode_004
theorem ridgeSupport608_suffix_decode_002 : PackedRawNatGrowth.readList 13 235 ridgeSupport608_rest_002 =
    (ridgeSupport608_suffix_002, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 203
    ridgeSupport608_rest_002 ridgeSupport608_rest_003 ridgeSupport608_rest_010
    ridgeSupport608_002 ridgeSupport608_suffix_003 ridgeSupport608_002_decode ridgeSupport608_suffix_decode_003
theorem ridgeSupport608_suffix_decode_001 : PackedRawNatGrowth.readList 13 267 ridgeSupport608_rest_001 =
    (ridgeSupport608_suffix_001, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 235
    ridgeSupport608_rest_001 ridgeSupport608_rest_002 ridgeSupport608_rest_010
    ridgeSupport608_001 ridgeSupport608_suffix_002 ridgeSupport608_001_decode ridgeSupport608_suffix_decode_002
theorem ridgeSupport608_suffix_decode_000 : PackedRawNatGrowth.readList 13 299 ridgeSupport608_rest_000 =
    (ridgeSupport608_suffix_000, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 267
    ridgeSupport608_rest_000 ridgeSupport608_rest_001 ridgeSupport608_rest_010
    ridgeSupport608_000 ridgeSupport608_suffix_001 ridgeSupport608_000_decode ridgeSupport608_suffix_decode_001
theorem ridgeSupport608_eq : candidateRows 608 = ridgeSupport608_suffix_000 := by
  change candidateSupports 608 = ridgeSupport608_suffix_000
  rw [ridgeSupport608_source]
  exact congrArg Prod.fst ridgeSupport608_suffix_decode_000
theorem ridgeTest_large_608 : ridgeTest 608 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport608_000_mask, ridgeSupport608_001_mask, ridgeSupport608_002_mask, ridgeSupport608_003_mask, ridgeSupport608_004_mask, ridgeSupport608_005_mask, ridgeSupport608_006_mask, ridgeSupport608_007_mask, ridgeSupport608_008_mask, ridgeSupport608_009_mask]
    decide +kernel
  · rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, List.all_append, List.all_nil, ridgeSupport608_000_checked, ridgeSupport608_001_checked, ridgeSupport608_002_checked, ridgeSupport608_003_checked, ridgeSupport608_004_checked, ridgeSupport608_005_checked, ridgeSupport608_006_checked, ridgeSupport608_007_checked, ridgeSupport608_008_checked, ridgeSupport608_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
