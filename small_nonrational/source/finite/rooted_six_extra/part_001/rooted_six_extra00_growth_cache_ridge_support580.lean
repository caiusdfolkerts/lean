module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport580Part000
public import RootedSixExtra00GrowthCacheRidgeSupport580Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport580_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport580_rest_016 =
    (ridgeSupport580_suffix_016, ridgeSupport580_rest_016) := by rfl
theorem ridgeSupport580_suffix_decode_015 : PackedRawNatGrowth.readList 14 19 ridgeSupport580_rest_015 =
    (ridgeSupport580_suffix_015, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 19 0
    ridgeSupport580_rest_015 ridgeSupport580_rest_016 ridgeSupport580_rest_016
    ridgeSupport580_015 ridgeSupport580_suffix_016 ridgeSupport580_015_decode ridgeSupport580_suffix_decode_016
theorem ridgeSupport580_suffix_decode_014 : PackedRawNatGrowth.readList 14 51 ridgeSupport580_rest_014 =
    (ridgeSupport580_suffix_014, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 19
    ridgeSupport580_rest_014 ridgeSupport580_rest_015 ridgeSupport580_rest_016
    ridgeSupport580_014 ridgeSupport580_suffix_015 ridgeSupport580_014_decode ridgeSupport580_suffix_decode_015
theorem ridgeSupport580_suffix_decode_013 : PackedRawNatGrowth.readList 14 83 ridgeSupport580_rest_013 =
    (ridgeSupport580_suffix_013, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 51
    ridgeSupport580_rest_013 ridgeSupport580_rest_014 ridgeSupport580_rest_016
    ridgeSupport580_013 ridgeSupport580_suffix_014 ridgeSupport580_013_decode ridgeSupport580_suffix_decode_014
theorem ridgeSupport580_suffix_decode_012 : PackedRawNatGrowth.readList 14 115 ridgeSupport580_rest_012 =
    (ridgeSupport580_suffix_012, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 83
    ridgeSupport580_rest_012 ridgeSupport580_rest_013 ridgeSupport580_rest_016
    ridgeSupport580_012 ridgeSupport580_suffix_013 ridgeSupport580_012_decode ridgeSupport580_suffix_decode_013
theorem ridgeSupport580_suffix_decode_011 : PackedRawNatGrowth.readList 14 147 ridgeSupport580_rest_011 =
    (ridgeSupport580_suffix_011, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 115
    ridgeSupport580_rest_011 ridgeSupport580_rest_012 ridgeSupport580_rest_016
    ridgeSupport580_011 ridgeSupport580_suffix_012 ridgeSupport580_011_decode ridgeSupport580_suffix_decode_012
theorem ridgeSupport580_suffix_decode_010 : PackedRawNatGrowth.readList 14 179 ridgeSupport580_rest_010 =
    (ridgeSupport580_suffix_010, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 147
    ridgeSupport580_rest_010 ridgeSupport580_rest_011 ridgeSupport580_rest_016
    ridgeSupport580_010 ridgeSupport580_suffix_011 ridgeSupport580_010_decode ridgeSupport580_suffix_decode_011
theorem ridgeSupport580_suffix_decode_009 : PackedRawNatGrowth.readList 14 211 ridgeSupport580_rest_009 =
    (ridgeSupport580_suffix_009, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 179
    ridgeSupport580_rest_009 ridgeSupport580_rest_010 ridgeSupport580_rest_016
    ridgeSupport580_009 ridgeSupport580_suffix_010 ridgeSupport580_009_decode ridgeSupport580_suffix_decode_010
theorem ridgeSupport580_suffix_decode_008 : PackedRawNatGrowth.readList 14 243 ridgeSupport580_rest_008 =
    (ridgeSupport580_suffix_008, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 211
    ridgeSupport580_rest_008 ridgeSupport580_rest_009 ridgeSupport580_rest_016
    ridgeSupport580_008 ridgeSupport580_suffix_009 ridgeSupport580_008_decode ridgeSupport580_suffix_decode_009
theorem ridgeSupport580_suffix_decode_007 : PackedRawNatGrowth.readList 14 275 ridgeSupport580_rest_007 =
    (ridgeSupport580_suffix_007, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 243
    ridgeSupport580_rest_007 ridgeSupport580_rest_008 ridgeSupport580_rest_016
    ridgeSupport580_007 ridgeSupport580_suffix_008 ridgeSupport580_007_decode ridgeSupport580_suffix_decode_008
theorem ridgeSupport580_suffix_decode_006 : PackedRawNatGrowth.readList 14 307 ridgeSupport580_rest_006 =
    (ridgeSupport580_suffix_006, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 275
    ridgeSupport580_rest_006 ridgeSupport580_rest_007 ridgeSupport580_rest_016
    ridgeSupport580_006 ridgeSupport580_suffix_007 ridgeSupport580_006_decode ridgeSupport580_suffix_decode_007
theorem ridgeSupport580_suffix_decode_005 : PackedRawNatGrowth.readList 14 339 ridgeSupport580_rest_005 =
    (ridgeSupport580_suffix_005, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 307
    ridgeSupport580_rest_005 ridgeSupport580_rest_006 ridgeSupport580_rest_016
    ridgeSupport580_005 ridgeSupport580_suffix_006 ridgeSupport580_005_decode ridgeSupport580_suffix_decode_006
theorem ridgeSupport580_suffix_decode_004 : PackedRawNatGrowth.readList 14 371 ridgeSupport580_rest_004 =
    (ridgeSupport580_suffix_004, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 339
    ridgeSupport580_rest_004 ridgeSupport580_rest_005 ridgeSupport580_rest_016
    ridgeSupport580_004 ridgeSupport580_suffix_005 ridgeSupport580_004_decode ridgeSupport580_suffix_decode_005
theorem ridgeSupport580_suffix_decode_003 : PackedRawNatGrowth.readList 14 403 ridgeSupport580_rest_003 =
    (ridgeSupport580_suffix_003, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 371
    ridgeSupport580_rest_003 ridgeSupport580_rest_004 ridgeSupport580_rest_016
    ridgeSupport580_003 ridgeSupport580_suffix_004 ridgeSupport580_003_decode ridgeSupport580_suffix_decode_004
theorem ridgeSupport580_suffix_decode_002 : PackedRawNatGrowth.readList 14 435 ridgeSupport580_rest_002 =
    (ridgeSupport580_suffix_002, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 403
    ridgeSupport580_rest_002 ridgeSupport580_rest_003 ridgeSupport580_rest_016
    ridgeSupport580_002 ridgeSupport580_suffix_003 ridgeSupport580_002_decode ridgeSupport580_suffix_decode_003
theorem ridgeSupport580_suffix_decode_001 : PackedRawNatGrowth.readList 14 467 ridgeSupport580_rest_001 =
    (ridgeSupport580_suffix_001, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 435
    ridgeSupport580_rest_001 ridgeSupport580_rest_002 ridgeSupport580_rest_016
    ridgeSupport580_001 ridgeSupport580_suffix_002 ridgeSupport580_001_decode ridgeSupport580_suffix_decode_002
theorem ridgeSupport580_suffix_decode_000 : PackedRawNatGrowth.readList 14 499 ridgeSupport580_rest_000 =
    (ridgeSupport580_suffix_000, ridgeSupport580_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 467
    ridgeSupport580_rest_000 ridgeSupport580_rest_001 ridgeSupport580_rest_016
    ridgeSupport580_000 ridgeSupport580_suffix_001 ridgeSupport580_000_decode ridgeSupport580_suffix_decode_001
theorem ridgeSupport580_eq : candidateRows 580 = ridgeSupport580_suffix_000 := by
  change candidateSupports 580 = ridgeSupport580_suffix_000
  rw [ridgeSupport580_source]
  exact congrArg Prod.fst ridgeSupport580_suffix_decode_000
theorem ridgeTest_large_580 : ridgeTest 580 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, ridgeSupport580_suffix_010, ridgeSupport580_suffix_011, ridgeSupport580_suffix_012, ridgeSupport580_suffix_013, ridgeSupport580_suffix_014, ridgeSupport580_suffix_015, ridgeSupport580_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport580_000_mask, ridgeSupport580_001_mask, ridgeSupport580_002_mask, ridgeSupport580_003_mask, ridgeSupport580_004_mask, ridgeSupport580_005_mask, ridgeSupport580_006_mask, ridgeSupport580_007_mask, ridgeSupport580_008_mask, ridgeSupport580_009_mask, ridgeSupport580_010_mask, ridgeSupport580_011_mask, ridgeSupport580_012_mask, ridgeSupport580_013_mask, ridgeSupport580_014_mask, ridgeSupport580_015_mask]
    decide +kernel
  · rw [ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, ridgeSupport580_suffix_010, ridgeSupport580_suffix_011, ridgeSupport580_suffix_012, ridgeSupport580_suffix_013, ridgeSupport580_suffix_014, ridgeSupport580_suffix_015, ridgeSupport580_suffix_016, List.all_append, List.all_nil, ridgeSupport580_000_checked, ridgeSupport580_001_checked, ridgeSupport580_002_checked, ridgeSupport580_003_checked, ridgeSupport580_004_checked, ridgeSupport580_005_checked, ridgeSupport580_006_checked, ridgeSupport580_007_checked, ridgeSupport580_008_checked, ridgeSupport580_009_checked, ridgeSupport580_010_checked, ridgeSupport580_011_checked, ridgeSupport580_012_checked, ridgeSupport580_013_checked, ridgeSupport580_014_checked, ridgeSupport580_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
