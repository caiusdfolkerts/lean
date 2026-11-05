module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport194Part000
public import RootedSixExtra00GrowthCacheRidgeSupport194Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport194_suffix_decode_013 : PackedRawNatGrowth.readList 14 0 ridgeSupport194_rest_013 =
    (ridgeSupport194_suffix_013, ridgeSupport194_rest_013) := by rfl
theorem ridgeSupport194_suffix_decode_012 : PackedRawNatGrowth.readList 14 18 ridgeSupport194_rest_012 =
    (ridgeSupport194_suffix_012, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 18 0
    ridgeSupport194_rest_012 ridgeSupport194_rest_013 ridgeSupport194_rest_013
    ridgeSupport194_012 ridgeSupport194_suffix_013 ridgeSupport194_012_decode ridgeSupport194_suffix_decode_013
theorem ridgeSupport194_suffix_decode_011 : PackedRawNatGrowth.readList 14 50 ridgeSupport194_rest_011 =
    (ridgeSupport194_suffix_011, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 18
    ridgeSupport194_rest_011 ridgeSupport194_rest_012 ridgeSupport194_rest_013
    ridgeSupport194_011 ridgeSupport194_suffix_012 ridgeSupport194_011_decode ridgeSupport194_suffix_decode_012
theorem ridgeSupport194_suffix_decode_010 : PackedRawNatGrowth.readList 14 82 ridgeSupport194_rest_010 =
    (ridgeSupport194_suffix_010, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 50
    ridgeSupport194_rest_010 ridgeSupport194_rest_011 ridgeSupport194_rest_013
    ridgeSupport194_010 ridgeSupport194_suffix_011 ridgeSupport194_010_decode ridgeSupport194_suffix_decode_011
theorem ridgeSupport194_suffix_decode_009 : PackedRawNatGrowth.readList 14 114 ridgeSupport194_rest_009 =
    (ridgeSupport194_suffix_009, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 82
    ridgeSupport194_rest_009 ridgeSupport194_rest_010 ridgeSupport194_rest_013
    ridgeSupport194_009 ridgeSupport194_suffix_010 ridgeSupport194_009_decode ridgeSupport194_suffix_decode_010
theorem ridgeSupport194_suffix_decode_008 : PackedRawNatGrowth.readList 14 146 ridgeSupport194_rest_008 =
    (ridgeSupport194_suffix_008, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 114
    ridgeSupport194_rest_008 ridgeSupport194_rest_009 ridgeSupport194_rest_013
    ridgeSupport194_008 ridgeSupport194_suffix_009 ridgeSupport194_008_decode ridgeSupport194_suffix_decode_009
theorem ridgeSupport194_suffix_decode_007 : PackedRawNatGrowth.readList 14 178 ridgeSupport194_rest_007 =
    (ridgeSupport194_suffix_007, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 146
    ridgeSupport194_rest_007 ridgeSupport194_rest_008 ridgeSupport194_rest_013
    ridgeSupport194_007 ridgeSupport194_suffix_008 ridgeSupport194_007_decode ridgeSupport194_suffix_decode_008
theorem ridgeSupport194_suffix_decode_006 : PackedRawNatGrowth.readList 14 210 ridgeSupport194_rest_006 =
    (ridgeSupport194_suffix_006, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 178
    ridgeSupport194_rest_006 ridgeSupport194_rest_007 ridgeSupport194_rest_013
    ridgeSupport194_006 ridgeSupport194_suffix_007 ridgeSupport194_006_decode ridgeSupport194_suffix_decode_007
theorem ridgeSupport194_suffix_decode_005 : PackedRawNatGrowth.readList 14 242 ridgeSupport194_rest_005 =
    (ridgeSupport194_suffix_005, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 210
    ridgeSupport194_rest_005 ridgeSupport194_rest_006 ridgeSupport194_rest_013
    ridgeSupport194_005 ridgeSupport194_suffix_006 ridgeSupport194_005_decode ridgeSupport194_suffix_decode_006
theorem ridgeSupport194_suffix_decode_004 : PackedRawNatGrowth.readList 14 274 ridgeSupport194_rest_004 =
    (ridgeSupport194_suffix_004, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 242
    ridgeSupport194_rest_004 ridgeSupport194_rest_005 ridgeSupport194_rest_013
    ridgeSupport194_004 ridgeSupport194_suffix_005 ridgeSupport194_004_decode ridgeSupport194_suffix_decode_005
theorem ridgeSupport194_suffix_decode_003 : PackedRawNatGrowth.readList 14 306 ridgeSupport194_rest_003 =
    (ridgeSupport194_suffix_003, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 274
    ridgeSupport194_rest_003 ridgeSupport194_rest_004 ridgeSupport194_rest_013
    ridgeSupport194_003 ridgeSupport194_suffix_004 ridgeSupport194_003_decode ridgeSupport194_suffix_decode_004
theorem ridgeSupport194_suffix_decode_002 : PackedRawNatGrowth.readList 14 338 ridgeSupport194_rest_002 =
    (ridgeSupport194_suffix_002, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 306
    ridgeSupport194_rest_002 ridgeSupport194_rest_003 ridgeSupport194_rest_013
    ridgeSupport194_002 ridgeSupport194_suffix_003 ridgeSupport194_002_decode ridgeSupport194_suffix_decode_003
theorem ridgeSupport194_suffix_decode_001 : PackedRawNatGrowth.readList 14 370 ridgeSupport194_rest_001 =
    (ridgeSupport194_suffix_001, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 338
    ridgeSupport194_rest_001 ridgeSupport194_rest_002 ridgeSupport194_rest_013
    ridgeSupport194_001 ridgeSupport194_suffix_002 ridgeSupport194_001_decode ridgeSupport194_suffix_decode_002
theorem ridgeSupport194_suffix_decode_000 : PackedRawNatGrowth.readList 14 402 ridgeSupport194_rest_000 =
    (ridgeSupport194_suffix_000, ridgeSupport194_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 370
    ridgeSupport194_rest_000 ridgeSupport194_rest_001 ridgeSupport194_rest_013
    ridgeSupport194_000 ridgeSupport194_suffix_001 ridgeSupport194_000_decode ridgeSupport194_suffix_decode_001
theorem ridgeSupport194_eq : candidateRows 194 = ridgeSupport194_suffix_000 := by
  change candidateSupports 194 = ridgeSupport194_suffix_000
  rw [ridgeSupport194_source]
  exact congrArg Prod.fst ridgeSupport194_suffix_decode_000
theorem ridgeTest_large_194 : ridgeTest 194 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport194_eq]
    simp only [ridgeSupport194_suffix_000, ridgeSupport194_suffix_001, ridgeSupport194_suffix_002, ridgeSupport194_suffix_003, ridgeSupport194_suffix_004, ridgeSupport194_suffix_005, ridgeSupport194_suffix_006, ridgeSupport194_suffix_007, ridgeSupport194_suffix_008, ridgeSupport194_suffix_009, ridgeSupport194_suffix_010, ridgeSupport194_suffix_011, ridgeSupport194_suffix_012, ridgeSupport194_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport194_000_mask, ridgeSupport194_001_mask, ridgeSupport194_002_mask, ridgeSupport194_003_mask, ridgeSupport194_004_mask, ridgeSupport194_005_mask, ridgeSupport194_006_mask, ridgeSupport194_007_mask, ridgeSupport194_008_mask, ridgeSupport194_009_mask, ridgeSupport194_010_mask, ridgeSupport194_011_mask, ridgeSupport194_012_mask]
    decide +kernel
  · rw [ridgeSupport194_eq]
    simp only [ridgeSupport194_suffix_000, ridgeSupport194_suffix_001, ridgeSupport194_suffix_002, ridgeSupport194_suffix_003, ridgeSupport194_suffix_004, ridgeSupport194_suffix_005, ridgeSupport194_suffix_006, ridgeSupport194_suffix_007, ridgeSupport194_suffix_008, ridgeSupport194_suffix_009, ridgeSupport194_suffix_010, ridgeSupport194_suffix_011, ridgeSupport194_suffix_012, ridgeSupport194_suffix_013, List.all_append, List.all_nil, ridgeSupport194_000_checked, ridgeSupport194_001_checked, ridgeSupport194_002_checked, ridgeSupport194_003_checked, ridgeSupport194_004_checked, ridgeSupport194_005_checked, ridgeSupport194_006_checked, ridgeSupport194_007_checked, ridgeSupport194_008_checked, ridgeSupport194_009_checked, ridgeSupport194_010_checked, ridgeSupport194_011_checked, ridgeSupport194_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
