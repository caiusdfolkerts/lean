module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport196Part000
public import RootedSixExtra00GrowthCacheRidgeSupport196Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport196_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport196_rest_016 =
    (ridgeSupport196_suffix_016, ridgeSupport196_rest_016) := by rfl
theorem ridgeSupport196_suffix_decode_015 : PackedRawNatGrowth.readList 14 19 ridgeSupport196_rest_015 =
    (ridgeSupport196_suffix_015, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 19 0
    ridgeSupport196_rest_015 ridgeSupport196_rest_016 ridgeSupport196_rest_016
    ridgeSupport196_015 ridgeSupport196_suffix_016 ridgeSupport196_015_decode ridgeSupport196_suffix_decode_016
theorem ridgeSupport196_suffix_decode_014 : PackedRawNatGrowth.readList 14 51 ridgeSupport196_rest_014 =
    (ridgeSupport196_suffix_014, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 19
    ridgeSupport196_rest_014 ridgeSupport196_rest_015 ridgeSupport196_rest_016
    ridgeSupport196_014 ridgeSupport196_suffix_015 ridgeSupport196_014_decode ridgeSupport196_suffix_decode_015
theorem ridgeSupport196_suffix_decode_013 : PackedRawNatGrowth.readList 14 83 ridgeSupport196_rest_013 =
    (ridgeSupport196_suffix_013, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 51
    ridgeSupport196_rest_013 ridgeSupport196_rest_014 ridgeSupport196_rest_016
    ridgeSupport196_013 ridgeSupport196_suffix_014 ridgeSupport196_013_decode ridgeSupport196_suffix_decode_014
theorem ridgeSupport196_suffix_decode_012 : PackedRawNatGrowth.readList 14 115 ridgeSupport196_rest_012 =
    (ridgeSupport196_suffix_012, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 83
    ridgeSupport196_rest_012 ridgeSupport196_rest_013 ridgeSupport196_rest_016
    ridgeSupport196_012 ridgeSupport196_suffix_013 ridgeSupport196_012_decode ridgeSupport196_suffix_decode_013
theorem ridgeSupport196_suffix_decode_011 : PackedRawNatGrowth.readList 14 147 ridgeSupport196_rest_011 =
    (ridgeSupport196_suffix_011, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 115
    ridgeSupport196_rest_011 ridgeSupport196_rest_012 ridgeSupport196_rest_016
    ridgeSupport196_011 ridgeSupport196_suffix_012 ridgeSupport196_011_decode ridgeSupport196_suffix_decode_012
theorem ridgeSupport196_suffix_decode_010 : PackedRawNatGrowth.readList 14 179 ridgeSupport196_rest_010 =
    (ridgeSupport196_suffix_010, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 147
    ridgeSupport196_rest_010 ridgeSupport196_rest_011 ridgeSupport196_rest_016
    ridgeSupport196_010 ridgeSupport196_suffix_011 ridgeSupport196_010_decode ridgeSupport196_suffix_decode_011
theorem ridgeSupport196_suffix_decode_009 : PackedRawNatGrowth.readList 14 211 ridgeSupport196_rest_009 =
    (ridgeSupport196_suffix_009, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 179
    ridgeSupport196_rest_009 ridgeSupport196_rest_010 ridgeSupport196_rest_016
    ridgeSupport196_009 ridgeSupport196_suffix_010 ridgeSupport196_009_decode ridgeSupport196_suffix_decode_010
theorem ridgeSupport196_suffix_decode_008 : PackedRawNatGrowth.readList 14 243 ridgeSupport196_rest_008 =
    (ridgeSupport196_suffix_008, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 211
    ridgeSupport196_rest_008 ridgeSupport196_rest_009 ridgeSupport196_rest_016
    ridgeSupport196_008 ridgeSupport196_suffix_009 ridgeSupport196_008_decode ridgeSupport196_suffix_decode_009
theorem ridgeSupport196_suffix_decode_007 : PackedRawNatGrowth.readList 14 275 ridgeSupport196_rest_007 =
    (ridgeSupport196_suffix_007, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 243
    ridgeSupport196_rest_007 ridgeSupport196_rest_008 ridgeSupport196_rest_016
    ridgeSupport196_007 ridgeSupport196_suffix_008 ridgeSupport196_007_decode ridgeSupport196_suffix_decode_008
theorem ridgeSupport196_suffix_decode_006 : PackedRawNatGrowth.readList 14 307 ridgeSupport196_rest_006 =
    (ridgeSupport196_suffix_006, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 275
    ridgeSupport196_rest_006 ridgeSupport196_rest_007 ridgeSupport196_rest_016
    ridgeSupport196_006 ridgeSupport196_suffix_007 ridgeSupport196_006_decode ridgeSupport196_suffix_decode_007
theorem ridgeSupport196_suffix_decode_005 : PackedRawNatGrowth.readList 14 339 ridgeSupport196_rest_005 =
    (ridgeSupport196_suffix_005, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 307
    ridgeSupport196_rest_005 ridgeSupport196_rest_006 ridgeSupport196_rest_016
    ridgeSupport196_005 ridgeSupport196_suffix_006 ridgeSupport196_005_decode ridgeSupport196_suffix_decode_006
theorem ridgeSupport196_suffix_decode_004 : PackedRawNatGrowth.readList 14 371 ridgeSupport196_rest_004 =
    (ridgeSupport196_suffix_004, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 339
    ridgeSupport196_rest_004 ridgeSupport196_rest_005 ridgeSupport196_rest_016
    ridgeSupport196_004 ridgeSupport196_suffix_005 ridgeSupport196_004_decode ridgeSupport196_suffix_decode_005
theorem ridgeSupport196_suffix_decode_003 : PackedRawNatGrowth.readList 14 403 ridgeSupport196_rest_003 =
    (ridgeSupport196_suffix_003, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 371
    ridgeSupport196_rest_003 ridgeSupport196_rest_004 ridgeSupport196_rest_016
    ridgeSupport196_003 ridgeSupport196_suffix_004 ridgeSupport196_003_decode ridgeSupport196_suffix_decode_004
theorem ridgeSupport196_suffix_decode_002 : PackedRawNatGrowth.readList 14 435 ridgeSupport196_rest_002 =
    (ridgeSupport196_suffix_002, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 403
    ridgeSupport196_rest_002 ridgeSupport196_rest_003 ridgeSupport196_rest_016
    ridgeSupport196_002 ridgeSupport196_suffix_003 ridgeSupport196_002_decode ridgeSupport196_suffix_decode_003
theorem ridgeSupport196_suffix_decode_001 : PackedRawNatGrowth.readList 14 467 ridgeSupport196_rest_001 =
    (ridgeSupport196_suffix_001, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 435
    ridgeSupport196_rest_001 ridgeSupport196_rest_002 ridgeSupport196_rest_016
    ridgeSupport196_001 ridgeSupport196_suffix_002 ridgeSupport196_001_decode ridgeSupport196_suffix_decode_002
theorem ridgeSupport196_suffix_decode_000 : PackedRawNatGrowth.readList 14 499 ridgeSupport196_rest_000 =
    (ridgeSupport196_suffix_000, ridgeSupport196_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 467
    ridgeSupport196_rest_000 ridgeSupport196_rest_001 ridgeSupport196_rest_016
    ridgeSupport196_000 ridgeSupport196_suffix_001 ridgeSupport196_000_decode ridgeSupport196_suffix_decode_001
theorem ridgeSupport196_eq : candidateRows 196 = ridgeSupport196_suffix_000 := by
  change candidateSupports 196 = ridgeSupport196_suffix_000
  rw [ridgeSupport196_source]
  exact congrArg Prod.fst ridgeSupport196_suffix_decode_000
theorem ridgeTest_large_196 : ridgeTest 196 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport196_eq]
    simp only [ridgeSupport196_suffix_000, ridgeSupport196_suffix_001, ridgeSupport196_suffix_002, ridgeSupport196_suffix_003, ridgeSupport196_suffix_004, ridgeSupport196_suffix_005, ridgeSupport196_suffix_006, ridgeSupport196_suffix_007, ridgeSupport196_suffix_008, ridgeSupport196_suffix_009, ridgeSupport196_suffix_010, ridgeSupport196_suffix_011, ridgeSupport196_suffix_012, ridgeSupport196_suffix_013, ridgeSupport196_suffix_014, ridgeSupport196_suffix_015, ridgeSupport196_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport196_000_mask, ridgeSupport196_001_mask, ridgeSupport196_002_mask, ridgeSupport196_003_mask, ridgeSupport196_004_mask, ridgeSupport196_005_mask, ridgeSupport196_006_mask, ridgeSupport196_007_mask, ridgeSupport196_008_mask, ridgeSupport196_009_mask, ridgeSupport196_010_mask, ridgeSupport196_011_mask, ridgeSupport196_012_mask, ridgeSupport196_013_mask, ridgeSupport196_014_mask, ridgeSupport196_015_mask]
    decide +kernel
  · rw [ridgeSupport196_eq]
    simp only [ridgeSupport196_suffix_000, ridgeSupport196_suffix_001, ridgeSupport196_suffix_002, ridgeSupport196_suffix_003, ridgeSupport196_suffix_004, ridgeSupport196_suffix_005, ridgeSupport196_suffix_006, ridgeSupport196_suffix_007, ridgeSupport196_suffix_008, ridgeSupport196_suffix_009, ridgeSupport196_suffix_010, ridgeSupport196_suffix_011, ridgeSupport196_suffix_012, ridgeSupport196_suffix_013, ridgeSupport196_suffix_014, ridgeSupport196_suffix_015, ridgeSupport196_suffix_016, List.all_append, List.all_nil, ridgeSupport196_000_checked, ridgeSupport196_001_checked, ridgeSupport196_002_checked, ridgeSupport196_003_checked, ridgeSupport196_004_checked, ridgeSupport196_005_checked, ridgeSupport196_006_checked, ridgeSupport196_007_checked, ridgeSupport196_008_checked, ridgeSupport196_009_checked, ridgeSupport196_010_checked, ridgeSupport196_011_checked, ridgeSupport196_012_checked, ridgeSupport196_013_checked, ridgeSupport196_014_checked, ridgeSupport196_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
