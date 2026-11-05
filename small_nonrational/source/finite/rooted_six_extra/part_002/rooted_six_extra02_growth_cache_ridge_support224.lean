module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport224Part000
public import RootedSixExtra02GrowthCacheRidgeSupport224Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport224_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport224_rest_010 =
    (ridgeSupport224_suffix_010, ridgeSupport224_rest_010) := by rfl
theorem ridgeSupport224_suffix_decode_009 : PackedRawNatGrowth.readList 13 11 ridgeSupport224_rest_009 =
    (ridgeSupport224_suffix_009, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 11 0
    ridgeSupport224_rest_009 ridgeSupport224_rest_010 ridgeSupport224_rest_010
    ridgeSupport224_009 ridgeSupport224_suffix_010 ridgeSupport224_009_decode ridgeSupport224_suffix_decode_010
theorem ridgeSupport224_suffix_decode_008 : PackedRawNatGrowth.readList 13 43 ridgeSupport224_rest_008 =
    (ridgeSupport224_suffix_008, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 11
    ridgeSupport224_rest_008 ridgeSupport224_rest_009 ridgeSupport224_rest_010
    ridgeSupport224_008 ridgeSupport224_suffix_009 ridgeSupport224_008_decode ridgeSupport224_suffix_decode_009
theorem ridgeSupport224_suffix_decode_007 : PackedRawNatGrowth.readList 13 75 ridgeSupport224_rest_007 =
    (ridgeSupport224_suffix_007, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 43
    ridgeSupport224_rest_007 ridgeSupport224_rest_008 ridgeSupport224_rest_010
    ridgeSupport224_007 ridgeSupport224_suffix_008 ridgeSupport224_007_decode ridgeSupport224_suffix_decode_008
theorem ridgeSupport224_suffix_decode_006 : PackedRawNatGrowth.readList 13 107 ridgeSupport224_rest_006 =
    (ridgeSupport224_suffix_006, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 75
    ridgeSupport224_rest_006 ridgeSupport224_rest_007 ridgeSupport224_rest_010
    ridgeSupport224_006 ridgeSupport224_suffix_007 ridgeSupport224_006_decode ridgeSupport224_suffix_decode_007
theorem ridgeSupport224_suffix_decode_005 : PackedRawNatGrowth.readList 13 139 ridgeSupport224_rest_005 =
    (ridgeSupport224_suffix_005, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 107
    ridgeSupport224_rest_005 ridgeSupport224_rest_006 ridgeSupport224_rest_010
    ridgeSupport224_005 ridgeSupport224_suffix_006 ridgeSupport224_005_decode ridgeSupport224_suffix_decode_006
theorem ridgeSupport224_suffix_decode_004 : PackedRawNatGrowth.readList 13 171 ridgeSupport224_rest_004 =
    (ridgeSupport224_suffix_004, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 139
    ridgeSupport224_rest_004 ridgeSupport224_rest_005 ridgeSupport224_rest_010
    ridgeSupport224_004 ridgeSupport224_suffix_005 ridgeSupport224_004_decode ridgeSupport224_suffix_decode_005
theorem ridgeSupport224_suffix_decode_003 : PackedRawNatGrowth.readList 13 203 ridgeSupport224_rest_003 =
    (ridgeSupport224_suffix_003, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 171
    ridgeSupport224_rest_003 ridgeSupport224_rest_004 ridgeSupport224_rest_010
    ridgeSupport224_003 ridgeSupport224_suffix_004 ridgeSupport224_003_decode ridgeSupport224_suffix_decode_004
theorem ridgeSupport224_suffix_decode_002 : PackedRawNatGrowth.readList 13 235 ridgeSupport224_rest_002 =
    (ridgeSupport224_suffix_002, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 203
    ridgeSupport224_rest_002 ridgeSupport224_rest_003 ridgeSupport224_rest_010
    ridgeSupport224_002 ridgeSupport224_suffix_003 ridgeSupport224_002_decode ridgeSupport224_suffix_decode_003
theorem ridgeSupport224_suffix_decode_001 : PackedRawNatGrowth.readList 13 267 ridgeSupport224_rest_001 =
    (ridgeSupport224_suffix_001, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 235
    ridgeSupport224_rest_001 ridgeSupport224_rest_002 ridgeSupport224_rest_010
    ridgeSupport224_001 ridgeSupport224_suffix_002 ridgeSupport224_001_decode ridgeSupport224_suffix_decode_002
theorem ridgeSupport224_suffix_decode_000 : PackedRawNatGrowth.readList 13 299 ridgeSupport224_rest_000 =
    (ridgeSupport224_suffix_000, ridgeSupport224_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 267
    ridgeSupport224_rest_000 ridgeSupport224_rest_001 ridgeSupport224_rest_010
    ridgeSupport224_000 ridgeSupport224_suffix_001 ridgeSupport224_000_decode ridgeSupport224_suffix_decode_001
theorem ridgeSupport224_eq : candidateRows 224 = ridgeSupport224_suffix_000 := by
  change candidateSupports 224 = ridgeSupport224_suffix_000
  rw [ridgeSupport224_source]
  exact congrArg Prod.fst ridgeSupport224_suffix_decode_000
theorem ridgeTest_large_224 : ridgeTest 224 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport224_eq]
    simp only [ridgeSupport224_suffix_000, ridgeSupport224_suffix_001, ridgeSupport224_suffix_002, ridgeSupport224_suffix_003, ridgeSupport224_suffix_004, ridgeSupport224_suffix_005, ridgeSupport224_suffix_006, ridgeSupport224_suffix_007, ridgeSupport224_suffix_008, ridgeSupport224_suffix_009, ridgeSupport224_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport224_000_mask, ridgeSupport224_001_mask, ridgeSupport224_002_mask, ridgeSupport224_003_mask, ridgeSupport224_004_mask, ridgeSupport224_005_mask, ridgeSupport224_006_mask, ridgeSupport224_007_mask, ridgeSupport224_008_mask, ridgeSupport224_009_mask]
    decide +kernel
  · rw [ridgeSupport224_eq]
    simp only [ridgeSupport224_suffix_000, ridgeSupport224_suffix_001, ridgeSupport224_suffix_002, ridgeSupport224_suffix_003, ridgeSupport224_suffix_004, ridgeSupport224_suffix_005, ridgeSupport224_suffix_006, ridgeSupport224_suffix_007, ridgeSupport224_suffix_008, ridgeSupport224_suffix_009, ridgeSupport224_suffix_010, List.all_append, List.all_nil, ridgeSupport224_000_checked, ridgeSupport224_001_checked, ridgeSupport224_002_checked, ridgeSupport224_003_checked, ridgeSupport224_004_checked, ridgeSupport224_005_checked, ridgeSupport224_006_checked, ridgeSupport224_007_checked, ridgeSupport224_008_checked, ridgeSupport224_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
