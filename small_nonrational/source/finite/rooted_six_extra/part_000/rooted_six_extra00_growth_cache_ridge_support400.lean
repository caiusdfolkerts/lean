module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport400Part000
public import RootedSixExtra00GrowthCacheRidgeSupport400Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport400_suffix_decode_013 : PackedRawNatGrowth.readList 14 0 ridgeSupport400_rest_013 =
    (ridgeSupport400_suffix_013, ridgeSupport400_rest_013) := by rfl
theorem ridgeSupport400_suffix_decode_012 : PackedRawNatGrowth.readList 14 18 ridgeSupport400_rest_012 =
    (ridgeSupport400_suffix_012, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 18 0
    ridgeSupport400_rest_012 ridgeSupport400_rest_013 ridgeSupport400_rest_013
    ridgeSupport400_012 ridgeSupport400_suffix_013 ridgeSupport400_012_decode ridgeSupport400_suffix_decode_013
theorem ridgeSupport400_suffix_decode_011 : PackedRawNatGrowth.readList 14 50 ridgeSupport400_rest_011 =
    (ridgeSupport400_suffix_011, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 18
    ridgeSupport400_rest_011 ridgeSupport400_rest_012 ridgeSupport400_rest_013
    ridgeSupport400_011 ridgeSupport400_suffix_012 ridgeSupport400_011_decode ridgeSupport400_suffix_decode_012
theorem ridgeSupport400_suffix_decode_010 : PackedRawNatGrowth.readList 14 82 ridgeSupport400_rest_010 =
    (ridgeSupport400_suffix_010, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 50
    ridgeSupport400_rest_010 ridgeSupport400_rest_011 ridgeSupport400_rest_013
    ridgeSupport400_010 ridgeSupport400_suffix_011 ridgeSupport400_010_decode ridgeSupport400_suffix_decode_011
theorem ridgeSupport400_suffix_decode_009 : PackedRawNatGrowth.readList 14 114 ridgeSupport400_rest_009 =
    (ridgeSupport400_suffix_009, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 82
    ridgeSupport400_rest_009 ridgeSupport400_rest_010 ridgeSupport400_rest_013
    ridgeSupport400_009 ridgeSupport400_suffix_010 ridgeSupport400_009_decode ridgeSupport400_suffix_decode_010
theorem ridgeSupport400_suffix_decode_008 : PackedRawNatGrowth.readList 14 146 ridgeSupport400_rest_008 =
    (ridgeSupport400_suffix_008, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 114
    ridgeSupport400_rest_008 ridgeSupport400_rest_009 ridgeSupport400_rest_013
    ridgeSupport400_008 ridgeSupport400_suffix_009 ridgeSupport400_008_decode ridgeSupport400_suffix_decode_009
theorem ridgeSupport400_suffix_decode_007 : PackedRawNatGrowth.readList 14 178 ridgeSupport400_rest_007 =
    (ridgeSupport400_suffix_007, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 146
    ridgeSupport400_rest_007 ridgeSupport400_rest_008 ridgeSupport400_rest_013
    ridgeSupport400_007 ridgeSupport400_suffix_008 ridgeSupport400_007_decode ridgeSupport400_suffix_decode_008
theorem ridgeSupport400_suffix_decode_006 : PackedRawNatGrowth.readList 14 210 ridgeSupport400_rest_006 =
    (ridgeSupport400_suffix_006, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 178
    ridgeSupport400_rest_006 ridgeSupport400_rest_007 ridgeSupport400_rest_013
    ridgeSupport400_006 ridgeSupport400_suffix_007 ridgeSupport400_006_decode ridgeSupport400_suffix_decode_007
theorem ridgeSupport400_suffix_decode_005 : PackedRawNatGrowth.readList 14 242 ridgeSupport400_rest_005 =
    (ridgeSupport400_suffix_005, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 210
    ridgeSupport400_rest_005 ridgeSupport400_rest_006 ridgeSupport400_rest_013
    ridgeSupport400_005 ridgeSupport400_suffix_006 ridgeSupport400_005_decode ridgeSupport400_suffix_decode_006
theorem ridgeSupport400_suffix_decode_004 : PackedRawNatGrowth.readList 14 274 ridgeSupport400_rest_004 =
    (ridgeSupport400_suffix_004, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 242
    ridgeSupport400_rest_004 ridgeSupport400_rest_005 ridgeSupport400_rest_013
    ridgeSupport400_004 ridgeSupport400_suffix_005 ridgeSupport400_004_decode ridgeSupport400_suffix_decode_005
theorem ridgeSupport400_suffix_decode_003 : PackedRawNatGrowth.readList 14 306 ridgeSupport400_rest_003 =
    (ridgeSupport400_suffix_003, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 274
    ridgeSupport400_rest_003 ridgeSupport400_rest_004 ridgeSupport400_rest_013
    ridgeSupport400_003 ridgeSupport400_suffix_004 ridgeSupport400_003_decode ridgeSupport400_suffix_decode_004
theorem ridgeSupport400_suffix_decode_002 : PackedRawNatGrowth.readList 14 338 ridgeSupport400_rest_002 =
    (ridgeSupport400_suffix_002, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 306
    ridgeSupport400_rest_002 ridgeSupport400_rest_003 ridgeSupport400_rest_013
    ridgeSupport400_002 ridgeSupport400_suffix_003 ridgeSupport400_002_decode ridgeSupport400_suffix_decode_003
theorem ridgeSupport400_suffix_decode_001 : PackedRawNatGrowth.readList 14 370 ridgeSupport400_rest_001 =
    (ridgeSupport400_suffix_001, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 338
    ridgeSupport400_rest_001 ridgeSupport400_rest_002 ridgeSupport400_rest_013
    ridgeSupport400_001 ridgeSupport400_suffix_002 ridgeSupport400_001_decode ridgeSupport400_suffix_decode_002
theorem ridgeSupport400_suffix_decode_000 : PackedRawNatGrowth.readList 14 402 ridgeSupport400_rest_000 =
    (ridgeSupport400_suffix_000, ridgeSupport400_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 370
    ridgeSupport400_rest_000 ridgeSupport400_rest_001 ridgeSupport400_rest_013
    ridgeSupport400_000 ridgeSupport400_suffix_001 ridgeSupport400_000_decode ridgeSupport400_suffix_decode_001
theorem ridgeSupport400_eq : candidateRows 400 = ridgeSupport400_suffix_000 := by
  change candidateSupports 400 = ridgeSupport400_suffix_000
  rw [ridgeSupport400_source]
  exact congrArg Prod.fst ridgeSupport400_suffix_decode_000
theorem ridgeTest_large_400 : ridgeTest 400 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport400_eq]
    simp only [ridgeSupport400_suffix_000, ridgeSupport400_suffix_001, ridgeSupport400_suffix_002, ridgeSupport400_suffix_003, ridgeSupport400_suffix_004, ridgeSupport400_suffix_005, ridgeSupport400_suffix_006, ridgeSupport400_suffix_007, ridgeSupport400_suffix_008, ridgeSupport400_suffix_009, ridgeSupport400_suffix_010, ridgeSupport400_suffix_011, ridgeSupport400_suffix_012, ridgeSupport400_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport400_000_mask, ridgeSupport400_001_mask, ridgeSupport400_002_mask, ridgeSupport400_003_mask, ridgeSupport400_004_mask, ridgeSupport400_005_mask, ridgeSupport400_006_mask, ridgeSupport400_007_mask, ridgeSupport400_008_mask, ridgeSupport400_009_mask, ridgeSupport400_010_mask, ridgeSupport400_011_mask, ridgeSupport400_012_mask]
    decide +kernel
  · rw [ridgeSupport400_eq]
    simp only [ridgeSupport400_suffix_000, ridgeSupport400_suffix_001, ridgeSupport400_suffix_002, ridgeSupport400_suffix_003, ridgeSupport400_suffix_004, ridgeSupport400_suffix_005, ridgeSupport400_suffix_006, ridgeSupport400_suffix_007, ridgeSupport400_suffix_008, ridgeSupport400_suffix_009, ridgeSupport400_suffix_010, ridgeSupport400_suffix_011, ridgeSupport400_suffix_012, ridgeSupport400_suffix_013, List.all_append, List.all_nil, ridgeSupport400_000_checked, ridgeSupport400_001_checked, ridgeSupport400_002_checked, ridgeSupport400_003_checked, ridgeSupport400_004_checked, ridgeSupport400_005_checked, ridgeSupport400_006_checked, ridgeSupport400_007_checked, ridgeSupport400_008_checked, ridgeSupport400_009_checked, ridgeSupport400_010_checked, ridgeSupport400_011_checked, ridgeSupport400_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
