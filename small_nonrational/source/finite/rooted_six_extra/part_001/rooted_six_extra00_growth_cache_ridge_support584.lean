module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport584Part000
public import RootedSixExtra00GrowthCacheRidgeSupport584Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport584_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport584_rest_016 =
    (ridgeSupport584_suffix_016, ridgeSupport584_rest_016) := by rfl
theorem ridgeSupport584_suffix_decode_015 : PackedRawNatGrowth.readList 14 19 ridgeSupport584_rest_015 =
    (ridgeSupport584_suffix_015, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 19 0
    ridgeSupport584_rest_015 ridgeSupport584_rest_016 ridgeSupport584_rest_016
    ridgeSupport584_015 ridgeSupport584_suffix_016 ridgeSupport584_015_decode ridgeSupport584_suffix_decode_016
theorem ridgeSupport584_suffix_decode_014 : PackedRawNatGrowth.readList 14 51 ridgeSupport584_rest_014 =
    (ridgeSupport584_suffix_014, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 19
    ridgeSupport584_rest_014 ridgeSupport584_rest_015 ridgeSupport584_rest_016
    ridgeSupport584_014 ridgeSupport584_suffix_015 ridgeSupport584_014_decode ridgeSupport584_suffix_decode_015
theorem ridgeSupport584_suffix_decode_013 : PackedRawNatGrowth.readList 14 83 ridgeSupport584_rest_013 =
    (ridgeSupport584_suffix_013, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 51
    ridgeSupport584_rest_013 ridgeSupport584_rest_014 ridgeSupport584_rest_016
    ridgeSupport584_013 ridgeSupport584_suffix_014 ridgeSupport584_013_decode ridgeSupport584_suffix_decode_014
theorem ridgeSupport584_suffix_decode_012 : PackedRawNatGrowth.readList 14 115 ridgeSupport584_rest_012 =
    (ridgeSupport584_suffix_012, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 83
    ridgeSupport584_rest_012 ridgeSupport584_rest_013 ridgeSupport584_rest_016
    ridgeSupport584_012 ridgeSupport584_suffix_013 ridgeSupport584_012_decode ridgeSupport584_suffix_decode_013
theorem ridgeSupport584_suffix_decode_011 : PackedRawNatGrowth.readList 14 147 ridgeSupport584_rest_011 =
    (ridgeSupport584_suffix_011, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 115
    ridgeSupport584_rest_011 ridgeSupport584_rest_012 ridgeSupport584_rest_016
    ridgeSupport584_011 ridgeSupport584_suffix_012 ridgeSupport584_011_decode ridgeSupport584_suffix_decode_012
theorem ridgeSupport584_suffix_decode_010 : PackedRawNatGrowth.readList 14 179 ridgeSupport584_rest_010 =
    (ridgeSupport584_suffix_010, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 147
    ridgeSupport584_rest_010 ridgeSupport584_rest_011 ridgeSupport584_rest_016
    ridgeSupport584_010 ridgeSupport584_suffix_011 ridgeSupport584_010_decode ridgeSupport584_suffix_decode_011
theorem ridgeSupport584_suffix_decode_009 : PackedRawNatGrowth.readList 14 211 ridgeSupport584_rest_009 =
    (ridgeSupport584_suffix_009, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 179
    ridgeSupport584_rest_009 ridgeSupport584_rest_010 ridgeSupport584_rest_016
    ridgeSupport584_009 ridgeSupport584_suffix_010 ridgeSupport584_009_decode ridgeSupport584_suffix_decode_010
theorem ridgeSupport584_suffix_decode_008 : PackedRawNatGrowth.readList 14 243 ridgeSupport584_rest_008 =
    (ridgeSupport584_suffix_008, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 211
    ridgeSupport584_rest_008 ridgeSupport584_rest_009 ridgeSupport584_rest_016
    ridgeSupport584_008 ridgeSupport584_suffix_009 ridgeSupport584_008_decode ridgeSupport584_suffix_decode_009
theorem ridgeSupport584_suffix_decode_007 : PackedRawNatGrowth.readList 14 275 ridgeSupport584_rest_007 =
    (ridgeSupport584_suffix_007, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 243
    ridgeSupport584_rest_007 ridgeSupport584_rest_008 ridgeSupport584_rest_016
    ridgeSupport584_007 ridgeSupport584_suffix_008 ridgeSupport584_007_decode ridgeSupport584_suffix_decode_008
theorem ridgeSupport584_suffix_decode_006 : PackedRawNatGrowth.readList 14 307 ridgeSupport584_rest_006 =
    (ridgeSupport584_suffix_006, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 275
    ridgeSupport584_rest_006 ridgeSupport584_rest_007 ridgeSupport584_rest_016
    ridgeSupport584_006 ridgeSupport584_suffix_007 ridgeSupport584_006_decode ridgeSupport584_suffix_decode_007
theorem ridgeSupport584_suffix_decode_005 : PackedRawNatGrowth.readList 14 339 ridgeSupport584_rest_005 =
    (ridgeSupport584_suffix_005, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 307
    ridgeSupport584_rest_005 ridgeSupport584_rest_006 ridgeSupport584_rest_016
    ridgeSupport584_005 ridgeSupport584_suffix_006 ridgeSupport584_005_decode ridgeSupport584_suffix_decode_006
theorem ridgeSupport584_suffix_decode_004 : PackedRawNatGrowth.readList 14 371 ridgeSupport584_rest_004 =
    (ridgeSupport584_suffix_004, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 339
    ridgeSupport584_rest_004 ridgeSupport584_rest_005 ridgeSupport584_rest_016
    ridgeSupport584_004 ridgeSupport584_suffix_005 ridgeSupport584_004_decode ridgeSupport584_suffix_decode_005
theorem ridgeSupport584_suffix_decode_003 : PackedRawNatGrowth.readList 14 403 ridgeSupport584_rest_003 =
    (ridgeSupport584_suffix_003, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 371
    ridgeSupport584_rest_003 ridgeSupport584_rest_004 ridgeSupport584_rest_016
    ridgeSupport584_003 ridgeSupport584_suffix_004 ridgeSupport584_003_decode ridgeSupport584_suffix_decode_004
theorem ridgeSupport584_suffix_decode_002 : PackedRawNatGrowth.readList 14 435 ridgeSupport584_rest_002 =
    (ridgeSupport584_suffix_002, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 403
    ridgeSupport584_rest_002 ridgeSupport584_rest_003 ridgeSupport584_rest_016
    ridgeSupport584_002 ridgeSupport584_suffix_003 ridgeSupport584_002_decode ridgeSupport584_suffix_decode_003
theorem ridgeSupport584_suffix_decode_001 : PackedRawNatGrowth.readList 14 467 ridgeSupport584_rest_001 =
    (ridgeSupport584_suffix_001, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 435
    ridgeSupport584_rest_001 ridgeSupport584_rest_002 ridgeSupport584_rest_016
    ridgeSupport584_001 ridgeSupport584_suffix_002 ridgeSupport584_001_decode ridgeSupport584_suffix_decode_002
theorem ridgeSupport584_suffix_decode_000 : PackedRawNatGrowth.readList 14 499 ridgeSupport584_rest_000 =
    (ridgeSupport584_suffix_000, ridgeSupport584_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 467
    ridgeSupport584_rest_000 ridgeSupport584_rest_001 ridgeSupport584_rest_016
    ridgeSupport584_000 ridgeSupport584_suffix_001 ridgeSupport584_000_decode ridgeSupport584_suffix_decode_001
theorem ridgeSupport584_eq : candidateRows 584 = ridgeSupport584_suffix_000 := by
  change candidateSupports 584 = ridgeSupport584_suffix_000
  rw [ridgeSupport584_source]
  exact congrArg Prod.fst ridgeSupport584_suffix_decode_000
theorem ridgeTest_large_584 : ridgeTest 584 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport584_eq]
    simp only [ridgeSupport584_suffix_000, ridgeSupport584_suffix_001, ridgeSupport584_suffix_002, ridgeSupport584_suffix_003, ridgeSupport584_suffix_004, ridgeSupport584_suffix_005, ridgeSupport584_suffix_006, ridgeSupport584_suffix_007, ridgeSupport584_suffix_008, ridgeSupport584_suffix_009, ridgeSupport584_suffix_010, ridgeSupport584_suffix_011, ridgeSupport584_suffix_012, ridgeSupport584_suffix_013, ridgeSupport584_suffix_014, ridgeSupport584_suffix_015, ridgeSupport584_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport584_000_mask, ridgeSupport584_001_mask, ridgeSupport584_002_mask, ridgeSupport584_003_mask, ridgeSupport584_004_mask, ridgeSupport584_005_mask, ridgeSupport584_006_mask, ridgeSupport584_007_mask, ridgeSupport584_008_mask, ridgeSupport584_009_mask, ridgeSupport584_010_mask, ridgeSupport584_011_mask, ridgeSupport584_012_mask, ridgeSupport584_013_mask, ridgeSupport584_014_mask, ridgeSupport584_015_mask]
    decide +kernel
  · rw [ridgeSupport584_eq]
    simp only [ridgeSupport584_suffix_000, ridgeSupport584_suffix_001, ridgeSupport584_suffix_002, ridgeSupport584_suffix_003, ridgeSupport584_suffix_004, ridgeSupport584_suffix_005, ridgeSupport584_suffix_006, ridgeSupport584_suffix_007, ridgeSupport584_suffix_008, ridgeSupport584_suffix_009, ridgeSupport584_suffix_010, ridgeSupport584_suffix_011, ridgeSupport584_suffix_012, ridgeSupport584_suffix_013, ridgeSupport584_suffix_014, ridgeSupport584_suffix_015, ridgeSupport584_suffix_016, List.all_append, List.all_nil, ridgeSupport584_000_checked, ridgeSupport584_001_checked, ridgeSupport584_002_checked, ridgeSupport584_003_checked, ridgeSupport584_004_checked, ridgeSupport584_005_checked, ridgeSupport584_006_checked, ridgeSupport584_007_checked, ridgeSupport584_008_checked, ridgeSupport584_009_checked, ridgeSupport584_010_checked, ridgeSupport584_011_checked, ridgeSupport584_012_checked, ridgeSupport584_013_checked, ridgeSupport584_014_checked, ridgeSupport584_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
