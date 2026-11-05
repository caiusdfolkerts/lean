module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport324Part000
public import RootedSixExtra00GrowthCacheRidgeSupport324Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport324_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport324_rest_016 =
    (ridgeSupport324_suffix_016, ridgeSupport324_rest_016) := by rfl
theorem ridgeSupport324_suffix_decode_015 : PackedRawNatGrowth.readList 14 19 ridgeSupport324_rest_015 =
    (ridgeSupport324_suffix_015, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 19 0
    ridgeSupport324_rest_015 ridgeSupport324_rest_016 ridgeSupport324_rest_016
    ridgeSupport324_015 ridgeSupport324_suffix_016 ridgeSupport324_015_decode ridgeSupport324_suffix_decode_016
theorem ridgeSupport324_suffix_decode_014 : PackedRawNatGrowth.readList 14 51 ridgeSupport324_rest_014 =
    (ridgeSupport324_suffix_014, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 19
    ridgeSupport324_rest_014 ridgeSupport324_rest_015 ridgeSupport324_rest_016
    ridgeSupport324_014 ridgeSupport324_suffix_015 ridgeSupport324_014_decode ridgeSupport324_suffix_decode_015
theorem ridgeSupport324_suffix_decode_013 : PackedRawNatGrowth.readList 14 83 ridgeSupport324_rest_013 =
    (ridgeSupport324_suffix_013, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 51
    ridgeSupport324_rest_013 ridgeSupport324_rest_014 ridgeSupport324_rest_016
    ridgeSupport324_013 ridgeSupport324_suffix_014 ridgeSupport324_013_decode ridgeSupport324_suffix_decode_014
theorem ridgeSupport324_suffix_decode_012 : PackedRawNatGrowth.readList 14 115 ridgeSupport324_rest_012 =
    (ridgeSupport324_suffix_012, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 83
    ridgeSupport324_rest_012 ridgeSupport324_rest_013 ridgeSupport324_rest_016
    ridgeSupport324_012 ridgeSupport324_suffix_013 ridgeSupport324_012_decode ridgeSupport324_suffix_decode_013
theorem ridgeSupport324_suffix_decode_011 : PackedRawNatGrowth.readList 14 147 ridgeSupport324_rest_011 =
    (ridgeSupport324_suffix_011, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 115
    ridgeSupport324_rest_011 ridgeSupport324_rest_012 ridgeSupport324_rest_016
    ridgeSupport324_011 ridgeSupport324_suffix_012 ridgeSupport324_011_decode ridgeSupport324_suffix_decode_012
theorem ridgeSupport324_suffix_decode_010 : PackedRawNatGrowth.readList 14 179 ridgeSupport324_rest_010 =
    (ridgeSupport324_suffix_010, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 147
    ridgeSupport324_rest_010 ridgeSupport324_rest_011 ridgeSupport324_rest_016
    ridgeSupport324_010 ridgeSupport324_suffix_011 ridgeSupport324_010_decode ridgeSupport324_suffix_decode_011
theorem ridgeSupport324_suffix_decode_009 : PackedRawNatGrowth.readList 14 211 ridgeSupport324_rest_009 =
    (ridgeSupport324_suffix_009, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 179
    ridgeSupport324_rest_009 ridgeSupport324_rest_010 ridgeSupport324_rest_016
    ridgeSupport324_009 ridgeSupport324_suffix_010 ridgeSupport324_009_decode ridgeSupport324_suffix_decode_010
theorem ridgeSupport324_suffix_decode_008 : PackedRawNatGrowth.readList 14 243 ridgeSupport324_rest_008 =
    (ridgeSupport324_suffix_008, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 211
    ridgeSupport324_rest_008 ridgeSupport324_rest_009 ridgeSupport324_rest_016
    ridgeSupport324_008 ridgeSupport324_suffix_009 ridgeSupport324_008_decode ridgeSupport324_suffix_decode_009
theorem ridgeSupport324_suffix_decode_007 : PackedRawNatGrowth.readList 14 275 ridgeSupport324_rest_007 =
    (ridgeSupport324_suffix_007, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 243
    ridgeSupport324_rest_007 ridgeSupport324_rest_008 ridgeSupport324_rest_016
    ridgeSupport324_007 ridgeSupport324_suffix_008 ridgeSupport324_007_decode ridgeSupport324_suffix_decode_008
theorem ridgeSupport324_suffix_decode_006 : PackedRawNatGrowth.readList 14 307 ridgeSupport324_rest_006 =
    (ridgeSupport324_suffix_006, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 275
    ridgeSupport324_rest_006 ridgeSupport324_rest_007 ridgeSupport324_rest_016
    ridgeSupport324_006 ridgeSupport324_suffix_007 ridgeSupport324_006_decode ridgeSupport324_suffix_decode_007
theorem ridgeSupport324_suffix_decode_005 : PackedRawNatGrowth.readList 14 339 ridgeSupport324_rest_005 =
    (ridgeSupport324_suffix_005, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 307
    ridgeSupport324_rest_005 ridgeSupport324_rest_006 ridgeSupport324_rest_016
    ridgeSupport324_005 ridgeSupport324_suffix_006 ridgeSupport324_005_decode ridgeSupport324_suffix_decode_006
theorem ridgeSupport324_suffix_decode_004 : PackedRawNatGrowth.readList 14 371 ridgeSupport324_rest_004 =
    (ridgeSupport324_suffix_004, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 339
    ridgeSupport324_rest_004 ridgeSupport324_rest_005 ridgeSupport324_rest_016
    ridgeSupport324_004 ridgeSupport324_suffix_005 ridgeSupport324_004_decode ridgeSupport324_suffix_decode_005
theorem ridgeSupport324_suffix_decode_003 : PackedRawNatGrowth.readList 14 403 ridgeSupport324_rest_003 =
    (ridgeSupport324_suffix_003, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 371
    ridgeSupport324_rest_003 ridgeSupport324_rest_004 ridgeSupport324_rest_016
    ridgeSupport324_003 ridgeSupport324_suffix_004 ridgeSupport324_003_decode ridgeSupport324_suffix_decode_004
theorem ridgeSupport324_suffix_decode_002 : PackedRawNatGrowth.readList 14 435 ridgeSupport324_rest_002 =
    (ridgeSupport324_suffix_002, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 403
    ridgeSupport324_rest_002 ridgeSupport324_rest_003 ridgeSupport324_rest_016
    ridgeSupport324_002 ridgeSupport324_suffix_003 ridgeSupport324_002_decode ridgeSupport324_suffix_decode_003
theorem ridgeSupport324_suffix_decode_001 : PackedRawNatGrowth.readList 14 467 ridgeSupport324_rest_001 =
    (ridgeSupport324_suffix_001, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 435
    ridgeSupport324_rest_001 ridgeSupport324_rest_002 ridgeSupport324_rest_016
    ridgeSupport324_001 ridgeSupport324_suffix_002 ridgeSupport324_001_decode ridgeSupport324_suffix_decode_002
theorem ridgeSupport324_suffix_decode_000 : PackedRawNatGrowth.readList 14 499 ridgeSupport324_rest_000 =
    (ridgeSupport324_suffix_000, ridgeSupport324_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 467
    ridgeSupport324_rest_000 ridgeSupport324_rest_001 ridgeSupport324_rest_016
    ridgeSupport324_000 ridgeSupport324_suffix_001 ridgeSupport324_000_decode ridgeSupport324_suffix_decode_001
theorem ridgeSupport324_eq : candidateRows 324 = ridgeSupport324_suffix_000 := by
  change candidateSupports 324 = ridgeSupport324_suffix_000
  rw [ridgeSupport324_source]
  exact congrArg Prod.fst ridgeSupport324_suffix_decode_000
theorem ridgeTest_large_324 : ridgeTest 324 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, ridgeSupport324_suffix_010, ridgeSupport324_suffix_011, ridgeSupport324_suffix_012, ridgeSupport324_suffix_013, ridgeSupport324_suffix_014, ridgeSupport324_suffix_015, ridgeSupport324_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport324_000_mask, ridgeSupport324_001_mask, ridgeSupport324_002_mask, ridgeSupport324_003_mask, ridgeSupport324_004_mask, ridgeSupport324_005_mask, ridgeSupport324_006_mask, ridgeSupport324_007_mask, ridgeSupport324_008_mask, ridgeSupport324_009_mask, ridgeSupport324_010_mask, ridgeSupport324_011_mask, ridgeSupport324_012_mask, ridgeSupport324_013_mask, ridgeSupport324_014_mask, ridgeSupport324_015_mask]
    decide +kernel
  · rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, ridgeSupport324_suffix_010, ridgeSupport324_suffix_011, ridgeSupport324_suffix_012, ridgeSupport324_suffix_013, ridgeSupport324_suffix_014, ridgeSupport324_suffix_015, ridgeSupport324_suffix_016, List.all_append, List.all_nil, ridgeSupport324_000_checked, ridgeSupport324_001_checked, ridgeSupport324_002_checked, ridgeSupport324_003_checked, ridgeSupport324_004_checked, ridgeSupport324_005_checked, ridgeSupport324_006_checked, ridgeSupport324_007_checked, ridgeSupport324_008_checked, ridgeSupport324_009_checked, ridgeSupport324_010_checked, ridgeSupport324_011_checked, ridgeSupport324_012_checked, ridgeSupport324_013_checked, ridgeSupport324_014_checked, ridgeSupport324_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
