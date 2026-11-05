module
prelude
public import RootedSixBase02GrowthCacheKindSupport9Part000
public import RootedSixBase02GrowthCacheKindSupport9Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport9_suffix_decode_016 : PackedRawNatGrowth.readList 13 0 kindSupport9_rest_016 =
    (kindSupport9_suffix_016, kindSupport9_rest_016) := by rfl
theorem kindSupport9_suffix_decode_015 : PackedRawNatGrowth.readList 13 24 kindSupport9_rest_015 =
    (kindSupport9_suffix_015, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 24 0
    kindSupport9_rest_015 kindSupport9_rest_016 kindSupport9_rest_016
    kindSupport9_015 kindSupport9_suffix_016 kindSupport9_015_decode kindSupport9_suffix_decode_016
theorem kindSupport9_suffix_decode_014 : PackedRawNatGrowth.readList 13 56 kindSupport9_rest_014 =
    (kindSupport9_suffix_014, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 24
    kindSupport9_rest_014 kindSupport9_rest_015 kindSupport9_rest_016
    kindSupport9_014 kindSupport9_suffix_015 kindSupport9_014_decode kindSupport9_suffix_decode_015
theorem kindSupport9_suffix_decode_013 : PackedRawNatGrowth.readList 13 88 kindSupport9_rest_013 =
    (kindSupport9_suffix_013, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 56
    kindSupport9_rest_013 kindSupport9_rest_014 kindSupport9_rest_016
    kindSupport9_013 kindSupport9_suffix_014 kindSupport9_013_decode kindSupport9_suffix_decode_014
theorem kindSupport9_suffix_decode_012 : PackedRawNatGrowth.readList 13 120 kindSupport9_rest_012 =
    (kindSupport9_suffix_012, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 88
    kindSupport9_rest_012 kindSupport9_rest_013 kindSupport9_rest_016
    kindSupport9_012 kindSupport9_suffix_013 kindSupport9_012_decode kindSupport9_suffix_decode_013
theorem kindSupport9_suffix_decode_011 : PackedRawNatGrowth.readList 13 152 kindSupport9_rest_011 =
    (kindSupport9_suffix_011, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 120
    kindSupport9_rest_011 kindSupport9_rest_012 kindSupport9_rest_016
    kindSupport9_011 kindSupport9_suffix_012 kindSupport9_011_decode kindSupport9_suffix_decode_012
theorem kindSupport9_suffix_decode_010 : PackedRawNatGrowth.readList 13 184 kindSupport9_rest_010 =
    (kindSupport9_suffix_010, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 152
    kindSupport9_rest_010 kindSupport9_rest_011 kindSupport9_rest_016
    kindSupport9_010 kindSupport9_suffix_011 kindSupport9_010_decode kindSupport9_suffix_decode_011
theorem kindSupport9_suffix_decode_009 : PackedRawNatGrowth.readList 13 216 kindSupport9_rest_009 =
    (kindSupport9_suffix_009, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 184
    kindSupport9_rest_009 kindSupport9_rest_010 kindSupport9_rest_016
    kindSupport9_009 kindSupport9_suffix_010 kindSupport9_009_decode kindSupport9_suffix_decode_010
theorem kindSupport9_suffix_decode_008 : PackedRawNatGrowth.readList 13 248 kindSupport9_rest_008 =
    (kindSupport9_suffix_008, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 216
    kindSupport9_rest_008 kindSupport9_rest_009 kindSupport9_rest_016
    kindSupport9_008 kindSupport9_suffix_009 kindSupport9_008_decode kindSupport9_suffix_decode_009
theorem kindSupport9_suffix_decode_007 : PackedRawNatGrowth.readList 13 280 kindSupport9_rest_007 =
    (kindSupport9_suffix_007, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 248
    kindSupport9_rest_007 kindSupport9_rest_008 kindSupport9_rest_016
    kindSupport9_007 kindSupport9_suffix_008 kindSupport9_007_decode kindSupport9_suffix_decode_008
theorem kindSupport9_suffix_decode_006 : PackedRawNatGrowth.readList 13 312 kindSupport9_rest_006 =
    (kindSupport9_suffix_006, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 280
    kindSupport9_rest_006 kindSupport9_rest_007 kindSupport9_rest_016
    kindSupport9_006 kindSupport9_suffix_007 kindSupport9_006_decode kindSupport9_suffix_decode_007
theorem kindSupport9_suffix_decode_005 : PackedRawNatGrowth.readList 13 344 kindSupport9_rest_005 =
    (kindSupport9_suffix_005, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 312
    kindSupport9_rest_005 kindSupport9_rest_006 kindSupport9_rest_016
    kindSupport9_005 kindSupport9_suffix_006 kindSupport9_005_decode kindSupport9_suffix_decode_006
theorem kindSupport9_suffix_decode_004 : PackedRawNatGrowth.readList 13 376 kindSupport9_rest_004 =
    (kindSupport9_suffix_004, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 344
    kindSupport9_rest_004 kindSupport9_rest_005 kindSupport9_rest_016
    kindSupport9_004 kindSupport9_suffix_005 kindSupport9_004_decode kindSupport9_suffix_decode_005
theorem kindSupport9_suffix_decode_003 : PackedRawNatGrowth.readList 13 408 kindSupport9_rest_003 =
    (kindSupport9_suffix_003, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 376
    kindSupport9_rest_003 kindSupport9_rest_004 kindSupport9_rest_016
    kindSupport9_003 kindSupport9_suffix_004 kindSupport9_003_decode kindSupport9_suffix_decode_004
theorem kindSupport9_suffix_decode_002 : PackedRawNatGrowth.readList 13 440 kindSupport9_rest_002 =
    (kindSupport9_suffix_002, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 408
    kindSupport9_rest_002 kindSupport9_rest_003 kindSupport9_rest_016
    kindSupport9_002 kindSupport9_suffix_003 kindSupport9_002_decode kindSupport9_suffix_decode_003
theorem kindSupport9_suffix_decode_001 : PackedRawNatGrowth.readList 13 472 kindSupport9_rest_001 =
    (kindSupport9_suffix_001, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 440
    kindSupport9_rest_001 kindSupport9_rest_002 kindSupport9_rest_016
    kindSupport9_001 kindSupport9_suffix_002 kindSupport9_001_decode kindSupport9_suffix_decode_002
theorem kindSupport9_suffix_decode_000 : PackedRawNatGrowth.readList 13 504 kindSupport9_rest_000 =
    (kindSupport9_suffix_000, kindSupport9_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 472
    kindSupport9_rest_000 kindSupport9_rest_001 kindSupport9_rest_016
    kindSupport9_000 kindSupport9_suffix_001 kindSupport9_000_decode kindSupport9_suffix_decode_001
theorem kindSupport9_eq : kindRows 9 = kindSupport9_suffix_000 := by
  change kindSupports 9 = kindSupport9_suffix_000
  rw [kindSupport9_source]
  exact congrArg Prod.fst kindSupport9_suffix_decode_000
theorem kindTest_large_9 : kindTest 9 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, kindSupport9_suffix_015, kindSupport9_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport9_000_mask, kindSupport9_001_mask, kindSupport9_002_mask, kindSupport9_003_mask, kindSupport9_004_mask, kindSupport9_005_mask, kindSupport9_006_mask, kindSupport9_007_mask, kindSupport9_008_mask, kindSupport9_009_mask, kindSupport9_010_mask, kindSupport9_011_mask, kindSupport9_012_mask, kindSupport9_013_mask, kindSupport9_014_mask, kindSupport9_015_mask]
    decide +kernel
  · rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, kindSupport9_suffix_015, kindSupport9_suffix_016, List.all_append, List.all_nil, kindSupport9_000_checked, kindSupport9_001_checked, kindSupport9_002_checked, kindSupport9_003_checked, kindSupport9_004_checked, kindSupport9_005_checked, kindSupport9_006_checked, kindSupport9_007_checked, kindSupport9_008_checked, kindSupport9_009_checked, kindSupport9_010_checked, kindSupport9_011_checked, kindSupport9_012_checked, kindSupport9_013_checked, kindSupport9_014_checked, kindSupport9_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
