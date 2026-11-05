module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport208Part000
public import RootedSixExtra00GrowthCacheRidgeSupport208Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport208_suffix_decode_013 : PackedRawNatGrowth.readList 14 0 ridgeSupport208_rest_013 =
    (ridgeSupport208_suffix_013, ridgeSupport208_rest_013) := by rfl
theorem ridgeSupport208_suffix_decode_012 : PackedRawNatGrowth.readList 14 18 ridgeSupport208_rest_012 =
    (ridgeSupport208_suffix_012, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 18 0
    ridgeSupport208_rest_012 ridgeSupport208_rest_013 ridgeSupport208_rest_013
    ridgeSupport208_012 ridgeSupport208_suffix_013 ridgeSupport208_012_decode ridgeSupport208_suffix_decode_013
theorem ridgeSupport208_suffix_decode_011 : PackedRawNatGrowth.readList 14 50 ridgeSupport208_rest_011 =
    (ridgeSupport208_suffix_011, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 18
    ridgeSupport208_rest_011 ridgeSupport208_rest_012 ridgeSupport208_rest_013
    ridgeSupport208_011 ridgeSupport208_suffix_012 ridgeSupport208_011_decode ridgeSupport208_suffix_decode_012
theorem ridgeSupport208_suffix_decode_010 : PackedRawNatGrowth.readList 14 82 ridgeSupport208_rest_010 =
    (ridgeSupport208_suffix_010, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 50
    ridgeSupport208_rest_010 ridgeSupport208_rest_011 ridgeSupport208_rest_013
    ridgeSupport208_010 ridgeSupport208_suffix_011 ridgeSupport208_010_decode ridgeSupport208_suffix_decode_011
theorem ridgeSupport208_suffix_decode_009 : PackedRawNatGrowth.readList 14 114 ridgeSupport208_rest_009 =
    (ridgeSupport208_suffix_009, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 82
    ridgeSupport208_rest_009 ridgeSupport208_rest_010 ridgeSupport208_rest_013
    ridgeSupport208_009 ridgeSupport208_suffix_010 ridgeSupport208_009_decode ridgeSupport208_suffix_decode_010
theorem ridgeSupport208_suffix_decode_008 : PackedRawNatGrowth.readList 14 146 ridgeSupport208_rest_008 =
    (ridgeSupport208_suffix_008, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 114
    ridgeSupport208_rest_008 ridgeSupport208_rest_009 ridgeSupport208_rest_013
    ridgeSupport208_008 ridgeSupport208_suffix_009 ridgeSupport208_008_decode ridgeSupport208_suffix_decode_009
theorem ridgeSupport208_suffix_decode_007 : PackedRawNatGrowth.readList 14 178 ridgeSupport208_rest_007 =
    (ridgeSupport208_suffix_007, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 146
    ridgeSupport208_rest_007 ridgeSupport208_rest_008 ridgeSupport208_rest_013
    ridgeSupport208_007 ridgeSupport208_suffix_008 ridgeSupport208_007_decode ridgeSupport208_suffix_decode_008
theorem ridgeSupport208_suffix_decode_006 : PackedRawNatGrowth.readList 14 210 ridgeSupport208_rest_006 =
    (ridgeSupport208_suffix_006, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 178
    ridgeSupport208_rest_006 ridgeSupport208_rest_007 ridgeSupport208_rest_013
    ridgeSupport208_006 ridgeSupport208_suffix_007 ridgeSupport208_006_decode ridgeSupport208_suffix_decode_007
theorem ridgeSupport208_suffix_decode_005 : PackedRawNatGrowth.readList 14 242 ridgeSupport208_rest_005 =
    (ridgeSupport208_suffix_005, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 210
    ridgeSupport208_rest_005 ridgeSupport208_rest_006 ridgeSupport208_rest_013
    ridgeSupport208_005 ridgeSupport208_suffix_006 ridgeSupport208_005_decode ridgeSupport208_suffix_decode_006
theorem ridgeSupport208_suffix_decode_004 : PackedRawNatGrowth.readList 14 274 ridgeSupport208_rest_004 =
    (ridgeSupport208_suffix_004, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 242
    ridgeSupport208_rest_004 ridgeSupport208_rest_005 ridgeSupport208_rest_013
    ridgeSupport208_004 ridgeSupport208_suffix_005 ridgeSupport208_004_decode ridgeSupport208_suffix_decode_005
theorem ridgeSupport208_suffix_decode_003 : PackedRawNatGrowth.readList 14 306 ridgeSupport208_rest_003 =
    (ridgeSupport208_suffix_003, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 274
    ridgeSupport208_rest_003 ridgeSupport208_rest_004 ridgeSupport208_rest_013
    ridgeSupport208_003 ridgeSupport208_suffix_004 ridgeSupport208_003_decode ridgeSupport208_suffix_decode_004
theorem ridgeSupport208_suffix_decode_002 : PackedRawNatGrowth.readList 14 338 ridgeSupport208_rest_002 =
    (ridgeSupport208_suffix_002, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 306
    ridgeSupport208_rest_002 ridgeSupport208_rest_003 ridgeSupport208_rest_013
    ridgeSupport208_002 ridgeSupport208_suffix_003 ridgeSupport208_002_decode ridgeSupport208_suffix_decode_003
theorem ridgeSupport208_suffix_decode_001 : PackedRawNatGrowth.readList 14 370 ridgeSupport208_rest_001 =
    (ridgeSupport208_suffix_001, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 338
    ridgeSupport208_rest_001 ridgeSupport208_rest_002 ridgeSupport208_rest_013
    ridgeSupport208_001 ridgeSupport208_suffix_002 ridgeSupport208_001_decode ridgeSupport208_suffix_decode_002
theorem ridgeSupport208_suffix_decode_000 : PackedRawNatGrowth.readList 14 402 ridgeSupport208_rest_000 =
    (ridgeSupport208_suffix_000, ridgeSupport208_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 370
    ridgeSupport208_rest_000 ridgeSupport208_rest_001 ridgeSupport208_rest_013
    ridgeSupport208_000 ridgeSupport208_suffix_001 ridgeSupport208_000_decode ridgeSupport208_suffix_decode_001
theorem ridgeSupport208_eq : candidateRows 208 = ridgeSupport208_suffix_000 := by
  change candidateSupports 208 = ridgeSupport208_suffix_000
  rw [ridgeSupport208_source]
  exact congrArg Prod.fst ridgeSupport208_suffix_decode_000
theorem ridgeTest_large_208 : ridgeTest 208 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport208_eq]
    simp only [ridgeSupport208_suffix_000, ridgeSupport208_suffix_001, ridgeSupport208_suffix_002, ridgeSupport208_suffix_003, ridgeSupport208_suffix_004, ridgeSupport208_suffix_005, ridgeSupport208_suffix_006, ridgeSupport208_suffix_007, ridgeSupport208_suffix_008, ridgeSupport208_suffix_009, ridgeSupport208_suffix_010, ridgeSupport208_suffix_011, ridgeSupport208_suffix_012, ridgeSupport208_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport208_000_mask, ridgeSupport208_001_mask, ridgeSupport208_002_mask, ridgeSupport208_003_mask, ridgeSupport208_004_mask, ridgeSupport208_005_mask, ridgeSupport208_006_mask, ridgeSupport208_007_mask, ridgeSupport208_008_mask, ridgeSupport208_009_mask, ridgeSupport208_010_mask, ridgeSupport208_011_mask, ridgeSupport208_012_mask]
    decide +kernel
  · rw [ridgeSupport208_eq]
    simp only [ridgeSupport208_suffix_000, ridgeSupport208_suffix_001, ridgeSupport208_suffix_002, ridgeSupport208_suffix_003, ridgeSupport208_suffix_004, ridgeSupport208_suffix_005, ridgeSupport208_suffix_006, ridgeSupport208_suffix_007, ridgeSupport208_suffix_008, ridgeSupport208_suffix_009, ridgeSupport208_suffix_010, ridgeSupport208_suffix_011, ridgeSupport208_suffix_012, ridgeSupport208_suffix_013, List.all_append, List.all_nil, ridgeSupport208_000_checked, ridgeSupport208_001_checked, ridgeSupport208_002_checked, ridgeSupport208_003_checked, ridgeSupport208_004_checked, ridgeSupport208_005_checked, ridgeSupport208_006_checked, ridgeSupport208_007_checked, ridgeSupport208_008_checked, ridgeSupport208_009_checked, ridgeSupport208_010_checked, ridgeSupport208_011_checked, ridgeSupport208_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
