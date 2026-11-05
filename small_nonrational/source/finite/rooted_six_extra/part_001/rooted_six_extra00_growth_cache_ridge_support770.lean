module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport770Part000
public import RootedSixExtra00GrowthCacheRidgeSupport770Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport770_suffix_decode_013 : PackedRawNatGrowth.readList 14 0 ridgeSupport770_rest_013 =
    (ridgeSupport770_suffix_013, ridgeSupport770_rest_013) := by rfl
theorem ridgeSupport770_suffix_decode_012 : PackedRawNatGrowth.readList 14 18 ridgeSupport770_rest_012 =
    (ridgeSupport770_suffix_012, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 18 0
    ridgeSupport770_rest_012 ridgeSupport770_rest_013 ridgeSupport770_rest_013
    ridgeSupport770_012 ridgeSupport770_suffix_013 ridgeSupport770_012_decode ridgeSupport770_suffix_decode_013
theorem ridgeSupport770_suffix_decode_011 : PackedRawNatGrowth.readList 14 50 ridgeSupport770_rest_011 =
    (ridgeSupport770_suffix_011, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 18
    ridgeSupport770_rest_011 ridgeSupport770_rest_012 ridgeSupport770_rest_013
    ridgeSupport770_011 ridgeSupport770_suffix_012 ridgeSupport770_011_decode ridgeSupport770_suffix_decode_012
theorem ridgeSupport770_suffix_decode_010 : PackedRawNatGrowth.readList 14 82 ridgeSupport770_rest_010 =
    (ridgeSupport770_suffix_010, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 50
    ridgeSupport770_rest_010 ridgeSupport770_rest_011 ridgeSupport770_rest_013
    ridgeSupport770_010 ridgeSupport770_suffix_011 ridgeSupport770_010_decode ridgeSupport770_suffix_decode_011
theorem ridgeSupport770_suffix_decode_009 : PackedRawNatGrowth.readList 14 114 ridgeSupport770_rest_009 =
    (ridgeSupport770_suffix_009, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 82
    ridgeSupport770_rest_009 ridgeSupport770_rest_010 ridgeSupport770_rest_013
    ridgeSupport770_009 ridgeSupport770_suffix_010 ridgeSupport770_009_decode ridgeSupport770_suffix_decode_010
theorem ridgeSupport770_suffix_decode_008 : PackedRawNatGrowth.readList 14 146 ridgeSupport770_rest_008 =
    (ridgeSupport770_suffix_008, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 114
    ridgeSupport770_rest_008 ridgeSupport770_rest_009 ridgeSupport770_rest_013
    ridgeSupport770_008 ridgeSupport770_suffix_009 ridgeSupport770_008_decode ridgeSupport770_suffix_decode_009
theorem ridgeSupport770_suffix_decode_007 : PackedRawNatGrowth.readList 14 178 ridgeSupport770_rest_007 =
    (ridgeSupport770_suffix_007, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 146
    ridgeSupport770_rest_007 ridgeSupport770_rest_008 ridgeSupport770_rest_013
    ridgeSupport770_007 ridgeSupport770_suffix_008 ridgeSupport770_007_decode ridgeSupport770_suffix_decode_008
theorem ridgeSupport770_suffix_decode_006 : PackedRawNatGrowth.readList 14 210 ridgeSupport770_rest_006 =
    (ridgeSupport770_suffix_006, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 178
    ridgeSupport770_rest_006 ridgeSupport770_rest_007 ridgeSupport770_rest_013
    ridgeSupport770_006 ridgeSupport770_suffix_007 ridgeSupport770_006_decode ridgeSupport770_suffix_decode_007
theorem ridgeSupport770_suffix_decode_005 : PackedRawNatGrowth.readList 14 242 ridgeSupport770_rest_005 =
    (ridgeSupport770_suffix_005, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 210
    ridgeSupport770_rest_005 ridgeSupport770_rest_006 ridgeSupport770_rest_013
    ridgeSupport770_005 ridgeSupport770_suffix_006 ridgeSupport770_005_decode ridgeSupport770_suffix_decode_006
theorem ridgeSupport770_suffix_decode_004 : PackedRawNatGrowth.readList 14 274 ridgeSupport770_rest_004 =
    (ridgeSupport770_suffix_004, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 242
    ridgeSupport770_rest_004 ridgeSupport770_rest_005 ridgeSupport770_rest_013
    ridgeSupport770_004 ridgeSupport770_suffix_005 ridgeSupport770_004_decode ridgeSupport770_suffix_decode_005
theorem ridgeSupport770_suffix_decode_003 : PackedRawNatGrowth.readList 14 306 ridgeSupport770_rest_003 =
    (ridgeSupport770_suffix_003, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 274
    ridgeSupport770_rest_003 ridgeSupport770_rest_004 ridgeSupport770_rest_013
    ridgeSupport770_003 ridgeSupport770_suffix_004 ridgeSupport770_003_decode ridgeSupport770_suffix_decode_004
theorem ridgeSupport770_suffix_decode_002 : PackedRawNatGrowth.readList 14 338 ridgeSupport770_rest_002 =
    (ridgeSupport770_suffix_002, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 306
    ridgeSupport770_rest_002 ridgeSupport770_rest_003 ridgeSupport770_rest_013
    ridgeSupport770_002 ridgeSupport770_suffix_003 ridgeSupport770_002_decode ridgeSupport770_suffix_decode_003
theorem ridgeSupport770_suffix_decode_001 : PackedRawNatGrowth.readList 14 370 ridgeSupport770_rest_001 =
    (ridgeSupport770_suffix_001, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 338
    ridgeSupport770_rest_001 ridgeSupport770_rest_002 ridgeSupport770_rest_013
    ridgeSupport770_001 ridgeSupport770_suffix_002 ridgeSupport770_001_decode ridgeSupport770_suffix_decode_002
theorem ridgeSupport770_suffix_decode_000 : PackedRawNatGrowth.readList 14 402 ridgeSupport770_rest_000 =
    (ridgeSupport770_suffix_000, ridgeSupport770_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 370
    ridgeSupport770_rest_000 ridgeSupport770_rest_001 ridgeSupport770_rest_013
    ridgeSupport770_000 ridgeSupport770_suffix_001 ridgeSupport770_000_decode ridgeSupport770_suffix_decode_001
theorem ridgeSupport770_eq : candidateRows 770 = ridgeSupport770_suffix_000 := by
  change candidateSupports 770 = ridgeSupport770_suffix_000
  rw [ridgeSupport770_source]
  exact congrArg Prod.fst ridgeSupport770_suffix_decode_000
theorem ridgeTest_large_770 : ridgeTest 770 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport770_eq]
    simp only [ridgeSupport770_suffix_000, ridgeSupport770_suffix_001, ridgeSupport770_suffix_002, ridgeSupport770_suffix_003, ridgeSupport770_suffix_004, ridgeSupport770_suffix_005, ridgeSupport770_suffix_006, ridgeSupport770_suffix_007, ridgeSupport770_suffix_008, ridgeSupport770_suffix_009, ridgeSupport770_suffix_010, ridgeSupport770_suffix_011, ridgeSupport770_suffix_012, ridgeSupport770_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport770_000_mask, ridgeSupport770_001_mask, ridgeSupport770_002_mask, ridgeSupport770_003_mask, ridgeSupport770_004_mask, ridgeSupport770_005_mask, ridgeSupport770_006_mask, ridgeSupport770_007_mask, ridgeSupport770_008_mask, ridgeSupport770_009_mask, ridgeSupport770_010_mask, ridgeSupport770_011_mask, ridgeSupport770_012_mask]
    decide +kernel
  · rw [ridgeSupport770_eq]
    simp only [ridgeSupport770_suffix_000, ridgeSupport770_suffix_001, ridgeSupport770_suffix_002, ridgeSupport770_suffix_003, ridgeSupport770_suffix_004, ridgeSupport770_suffix_005, ridgeSupport770_suffix_006, ridgeSupport770_suffix_007, ridgeSupport770_suffix_008, ridgeSupport770_suffix_009, ridgeSupport770_suffix_010, ridgeSupport770_suffix_011, ridgeSupport770_suffix_012, ridgeSupport770_suffix_013, List.all_append, List.all_nil, ridgeSupport770_000_checked, ridgeSupport770_001_checked, ridgeSupport770_002_checked, ridgeSupport770_003_checked, ridgeSupport770_004_checked, ridgeSupport770_005_checked, ridgeSupport770_006_checked, ridgeSupport770_007_checked, ridgeSupport770_008_checked, ridgeSupport770_009_checked, ridgeSupport770_010_checked, ridgeSupport770_011_checked, ridgeSupport770_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
