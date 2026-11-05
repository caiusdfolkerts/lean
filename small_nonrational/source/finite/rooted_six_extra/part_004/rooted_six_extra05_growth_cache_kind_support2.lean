module
prelude
public import RootedSixExtra05GrowthCacheKindSupport2Part000
public import RootedSixExtra05GrowthCacheKindSupport2Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_suffix_decode_015 : PackedRawNatGrowth.readList 12 0 kindSupport2_rest_015 =
    (kindSupport2_suffix_015, kindSupport2_rest_015) := by rfl
theorem kindSupport2_suffix_decode_014 : PackedRawNatGrowth.readList 12 8 kindSupport2_rest_014 =
    (kindSupport2_suffix_014, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 8 0
    kindSupport2_rest_014 kindSupport2_rest_015 kindSupport2_rest_015
    kindSupport2_014 kindSupport2_suffix_015 kindSupport2_014_decode kindSupport2_suffix_decode_015
theorem kindSupport2_suffix_decode_013 : PackedRawNatGrowth.readList 12 40 kindSupport2_rest_013 =
    (kindSupport2_suffix_013, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 8
    kindSupport2_rest_013 kindSupport2_rest_014 kindSupport2_rest_015
    kindSupport2_013 kindSupport2_suffix_014 kindSupport2_013_decode kindSupport2_suffix_decode_014
theorem kindSupport2_suffix_decode_012 : PackedRawNatGrowth.readList 12 72 kindSupport2_rest_012 =
    (kindSupport2_suffix_012, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 40
    kindSupport2_rest_012 kindSupport2_rest_013 kindSupport2_rest_015
    kindSupport2_012 kindSupport2_suffix_013 kindSupport2_012_decode kindSupport2_suffix_decode_013
theorem kindSupport2_suffix_decode_011 : PackedRawNatGrowth.readList 12 104 kindSupport2_rest_011 =
    (kindSupport2_suffix_011, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 72
    kindSupport2_rest_011 kindSupport2_rest_012 kindSupport2_rest_015
    kindSupport2_011 kindSupport2_suffix_012 kindSupport2_011_decode kindSupport2_suffix_decode_012
theorem kindSupport2_suffix_decode_010 : PackedRawNatGrowth.readList 12 136 kindSupport2_rest_010 =
    (kindSupport2_suffix_010, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 104
    kindSupport2_rest_010 kindSupport2_rest_011 kindSupport2_rest_015
    kindSupport2_010 kindSupport2_suffix_011 kindSupport2_010_decode kindSupport2_suffix_decode_011
theorem kindSupport2_suffix_decode_009 : PackedRawNatGrowth.readList 12 168 kindSupport2_rest_009 =
    (kindSupport2_suffix_009, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 136
    kindSupport2_rest_009 kindSupport2_rest_010 kindSupport2_rest_015
    kindSupport2_009 kindSupport2_suffix_010 kindSupport2_009_decode kindSupport2_suffix_decode_010
theorem kindSupport2_suffix_decode_008 : PackedRawNatGrowth.readList 12 200 kindSupport2_rest_008 =
    (kindSupport2_suffix_008, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 168
    kindSupport2_rest_008 kindSupport2_rest_009 kindSupport2_rest_015
    kindSupport2_008 kindSupport2_suffix_009 kindSupport2_008_decode kindSupport2_suffix_decode_009
theorem kindSupport2_suffix_decode_007 : PackedRawNatGrowth.readList 12 232 kindSupport2_rest_007 =
    (kindSupport2_suffix_007, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 200
    kindSupport2_rest_007 kindSupport2_rest_008 kindSupport2_rest_015
    kindSupport2_007 kindSupport2_suffix_008 kindSupport2_007_decode kindSupport2_suffix_decode_008
theorem kindSupport2_suffix_decode_006 : PackedRawNatGrowth.readList 12 264 kindSupport2_rest_006 =
    (kindSupport2_suffix_006, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 232
    kindSupport2_rest_006 kindSupport2_rest_007 kindSupport2_rest_015
    kindSupport2_006 kindSupport2_suffix_007 kindSupport2_006_decode kindSupport2_suffix_decode_007
theorem kindSupport2_suffix_decode_005 : PackedRawNatGrowth.readList 12 296 kindSupport2_rest_005 =
    (kindSupport2_suffix_005, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 264
    kindSupport2_rest_005 kindSupport2_rest_006 kindSupport2_rest_015
    kindSupport2_005 kindSupport2_suffix_006 kindSupport2_005_decode kindSupport2_suffix_decode_006
theorem kindSupport2_suffix_decode_004 : PackedRawNatGrowth.readList 12 328 kindSupport2_rest_004 =
    (kindSupport2_suffix_004, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 296
    kindSupport2_rest_004 kindSupport2_rest_005 kindSupport2_rest_015
    kindSupport2_004 kindSupport2_suffix_005 kindSupport2_004_decode kindSupport2_suffix_decode_005
theorem kindSupport2_suffix_decode_003 : PackedRawNatGrowth.readList 12 360 kindSupport2_rest_003 =
    (kindSupport2_suffix_003, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 328
    kindSupport2_rest_003 kindSupport2_rest_004 kindSupport2_rest_015
    kindSupport2_003 kindSupport2_suffix_004 kindSupport2_003_decode kindSupport2_suffix_decode_004
theorem kindSupport2_suffix_decode_002 : PackedRawNatGrowth.readList 12 392 kindSupport2_rest_002 =
    (kindSupport2_suffix_002, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 360
    kindSupport2_rest_002 kindSupport2_rest_003 kindSupport2_rest_015
    kindSupport2_002 kindSupport2_suffix_003 kindSupport2_002_decode kindSupport2_suffix_decode_003
theorem kindSupport2_suffix_decode_001 : PackedRawNatGrowth.readList 12 424 kindSupport2_rest_001 =
    (kindSupport2_suffix_001, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 392
    kindSupport2_rest_001 kindSupport2_rest_002 kindSupport2_rest_015
    kindSupport2_001 kindSupport2_suffix_002 kindSupport2_001_decode kindSupport2_suffix_decode_002
theorem kindSupport2_suffix_decode_000 : PackedRawNatGrowth.readList 12 456 kindSupport2_rest_000 =
    (kindSupport2_suffix_000, kindSupport2_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 424
    kindSupport2_rest_000 kindSupport2_rest_001 kindSupport2_rest_015
    kindSupport2_000 kindSupport2_suffix_001 kindSupport2_000_decode kindSupport2_suffix_decode_001
theorem kindSupport2_eq : kindRows 2 = kindSupport2_suffix_000 := by
  change kindSupports 2 = kindSupport2_suffix_000
  rw [kindSupport2_source]
  exact congrArg Prod.fst kindSupport2_suffix_decode_000
theorem kindTest_large_2 : kindTest 2 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport2_000_mask, kindSupport2_001_mask, kindSupport2_002_mask, kindSupport2_003_mask, kindSupport2_004_mask, kindSupport2_005_mask, kindSupport2_006_mask, kindSupport2_007_mask, kindSupport2_008_mask, kindSupport2_009_mask, kindSupport2_010_mask, kindSupport2_011_mask, kindSupport2_012_mask, kindSupport2_013_mask, kindSupport2_014_mask]
    decide +kernel
  · rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, List.all_append, List.all_nil, kindSupport2_000_checked, kindSupport2_001_checked, kindSupport2_002_checked, kindSupport2_003_checked, kindSupport2_004_checked, kindSupport2_005_checked, kindSupport2_006_checked, kindSupport2_007_checked, kindSupport2_008_checked, kindSupport2_009_checked, kindSupport2_010_checked, kindSupport2_011_checked, kindSupport2_012_checked, kindSupport2_013_checked, kindSupport2_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
