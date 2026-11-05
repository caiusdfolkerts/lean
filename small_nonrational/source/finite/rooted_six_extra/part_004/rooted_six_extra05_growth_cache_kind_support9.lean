module
prelude
public import RootedSixExtra05GrowthCacheKindSupport9Part000
public import RootedSixExtra05GrowthCacheKindSupport9Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport9_suffix_decode_014 : PackedRawNatGrowth.readList 12 0 kindSupport9_rest_014 =
    (kindSupport9_suffix_014, kindSupport9_rest_014) := by rfl
theorem kindSupport9_suffix_decode_013 : PackedRawNatGrowth.readList 12 28 kindSupport9_rest_013 =
    (kindSupport9_suffix_013, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 28 0
    kindSupport9_rest_013 kindSupport9_rest_014 kindSupport9_rest_014
    kindSupport9_013 kindSupport9_suffix_014 kindSupport9_013_decode kindSupport9_suffix_decode_014
theorem kindSupport9_suffix_decode_012 : PackedRawNatGrowth.readList 12 60 kindSupport9_rest_012 =
    (kindSupport9_suffix_012, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 28
    kindSupport9_rest_012 kindSupport9_rest_013 kindSupport9_rest_014
    kindSupport9_012 kindSupport9_suffix_013 kindSupport9_012_decode kindSupport9_suffix_decode_013
theorem kindSupport9_suffix_decode_011 : PackedRawNatGrowth.readList 12 92 kindSupport9_rest_011 =
    (kindSupport9_suffix_011, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 60
    kindSupport9_rest_011 kindSupport9_rest_012 kindSupport9_rest_014
    kindSupport9_011 kindSupport9_suffix_012 kindSupport9_011_decode kindSupport9_suffix_decode_012
theorem kindSupport9_suffix_decode_010 : PackedRawNatGrowth.readList 12 124 kindSupport9_rest_010 =
    (kindSupport9_suffix_010, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 92
    kindSupport9_rest_010 kindSupport9_rest_011 kindSupport9_rest_014
    kindSupport9_010 kindSupport9_suffix_011 kindSupport9_010_decode kindSupport9_suffix_decode_011
theorem kindSupport9_suffix_decode_009 : PackedRawNatGrowth.readList 12 156 kindSupport9_rest_009 =
    (kindSupport9_suffix_009, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 124
    kindSupport9_rest_009 kindSupport9_rest_010 kindSupport9_rest_014
    kindSupport9_009 kindSupport9_suffix_010 kindSupport9_009_decode kindSupport9_suffix_decode_010
theorem kindSupport9_suffix_decode_008 : PackedRawNatGrowth.readList 12 188 kindSupport9_rest_008 =
    (kindSupport9_suffix_008, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 156
    kindSupport9_rest_008 kindSupport9_rest_009 kindSupport9_rest_014
    kindSupport9_008 kindSupport9_suffix_009 kindSupport9_008_decode kindSupport9_suffix_decode_009
theorem kindSupport9_suffix_decode_007 : PackedRawNatGrowth.readList 12 220 kindSupport9_rest_007 =
    (kindSupport9_suffix_007, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 188
    kindSupport9_rest_007 kindSupport9_rest_008 kindSupport9_rest_014
    kindSupport9_007 kindSupport9_suffix_008 kindSupport9_007_decode kindSupport9_suffix_decode_008
theorem kindSupport9_suffix_decode_006 : PackedRawNatGrowth.readList 12 252 kindSupport9_rest_006 =
    (kindSupport9_suffix_006, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 220
    kindSupport9_rest_006 kindSupport9_rest_007 kindSupport9_rest_014
    kindSupport9_006 kindSupport9_suffix_007 kindSupport9_006_decode kindSupport9_suffix_decode_007
theorem kindSupport9_suffix_decode_005 : PackedRawNatGrowth.readList 12 284 kindSupport9_rest_005 =
    (kindSupport9_suffix_005, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 252
    kindSupport9_rest_005 kindSupport9_rest_006 kindSupport9_rest_014
    kindSupport9_005 kindSupport9_suffix_006 kindSupport9_005_decode kindSupport9_suffix_decode_006
theorem kindSupport9_suffix_decode_004 : PackedRawNatGrowth.readList 12 316 kindSupport9_rest_004 =
    (kindSupport9_suffix_004, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 284
    kindSupport9_rest_004 kindSupport9_rest_005 kindSupport9_rest_014
    kindSupport9_004 kindSupport9_suffix_005 kindSupport9_004_decode kindSupport9_suffix_decode_005
theorem kindSupport9_suffix_decode_003 : PackedRawNatGrowth.readList 12 348 kindSupport9_rest_003 =
    (kindSupport9_suffix_003, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 316
    kindSupport9_rest_003 kindSupport9_rest_004 kindSupport9_rest_014
    kindSupport9_003 kindSupport9_suffix_004 kindSupport9_003_decode kindSupport9_suffix_decode_004
theorem kindSupport9_suffix_decode_002 : PackedRawNatGrowth.readList 12 380 kindSupport9_rest_002 =
    (kindSupport9_suffix_002, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 348
    kindSupport9_rest_002 kindSupport9_rest_003 kindSupport9_rest_014
    kindSupport9_002 kindSupport9_suffix_003 kindSupport9_002_decode kindSupport9_suffix_decode_003
theorem kindSupport9_suffix_decode_001 : PackedRawNatGrowth.readList 12 412 kindSupport9_rest_001 =
    (kindSupport9_suffix_001, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 380
    kindSupport9_rest_001 kindSupport9_rest_002 kindSupport9_rest_014
    kindSupport9_001 kindSupport9_suffix_002 kindSupport9_001_decode kindSupport9_suffix_decode_002
theorem kindSupport9_suffix_decode_000 : PackedRawNatGrowth.readList 12 444 kindSupport9_rest_000 =
    (kindSupport9_suffix_000, kindSupport9_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 412
    kindSupport9_rest_000 kindSupport9_rest_001 kindSupport9_rest_014
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
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport9_000_mask, kindSupport9_001_mask, kindSupport9_002_mask, kindSupport9_003_mask, kindSupport9_004_mask, kindSupport9_005_mask, kindSupport9_006_mask, kindSupport9_007_mask, kindSupport9_008_mask, kindSupport9_009_mask, kindSupport9_010_mask, kindSupport9_011_mask, kindSupport9_012_mask, kindSupport9_013_mask]
    decide +kernel
  · rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, List.all_append, List.all_nil, kindSupport9_000_checked, kindSupport9_001_checked, kindSupport9_002_checked, kindSupport9_003_checked, kindSupport9_004_checked, kindSupport9_005_checked, kindSupport9_006_checked, kindSupport9_007_checked, kindSupport9_008_checked, kindSupport9_009_checked, kindSupport9_010_checked, kindSupport9_011_checked, kindSupport9_012_checked, kindSupport9_013_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
