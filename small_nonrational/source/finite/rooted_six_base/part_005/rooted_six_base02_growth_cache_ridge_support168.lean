module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport168Part000
public import RootedSixBase02GrowthCacheRidgeSupport168Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport168_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport168_rest_012 =
    (ridgeSupport168_suffix_012, ridgeSupport168_rest_012) := by rfl
theorem ridgeSupport168_suffix_decode_011 : PackedRawNatGrowth.readList 13 25 ridgeSupport168_rest_011 =
    (ridgeSupport168_suffix_011, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 25 0
    ridgeSupport168_rest_011 ridgeSupport168_rest_012 ridgeSupport168_rest_012
    ridgeSupport168_011 ridgeSupport168_suffix_012 ridgeSupport168_011_decode ridgeSupport168_suffix_decode_012
theorem ridgeSupport168_suffix_decode_010 : PackedRawNatGrowth.readList 13 57 ridgeSupport168_rest_010 =
    (ridgeSupport168_suffix_010, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 25
    ridgeSupport168_rest_010 ridgeSupport168_rest_011 ridgeSupport168_rest_012
    ridgeSupport168_010 ridgeSupport168_suffix_011 ridgeSupport168_010_decode ridgeSupport168_suffix_decode_011
theorem ridgeSupport168_suffix_decode_009 : PackedRawNatGrowth.readList 13 89 ridgeSupport168_rest_009 =
    (ridgeSupport168_suffix_009, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 57
    ridgeSupport168_rest_009 ridgeSupport168_rest_010 ridgeSupport168_rest_012
    ridgeSupport168_009 ridgeSupport168_suffix_010 ridgeSupport168_009_decode ridgeSupport168_suffix_decode_010
theorem ridgeSupport168_suffix_decode_008 : PackedRawNatGrowth.readList 13 121 ridgeSupport168_rest_008 =
    (ridgeSupport168_suffix_008, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 89
    ridgeSupport168_rest_008 ridgeSupport168_rest_009 ridgeSupport168_rest_012
    ridgeSupport168_008 ridgeSupport168_suffix_009 ridgeSupport168_008_decode ridgeSupport168_suffix_decode_009
theorem ridgeSupport168_suffix_decode_007 : PackedRawNatGrowth.readList 13 153 ridgeSupport168_rest_007 =
    (ridgeSupport168_suffix_007, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 121
    ridgeSupport168_rest_007 ridgeSupport168_rest_008 ridgeSupport168_rest_012
    ridgeSupport168_007 ridgeSupport168_suffix_008 ridgeSupport168_007_decode ridgeSupport168_suffix_decode_008
theorem ridgeSupport168_suffix_decode_006 : PackedRawNatGrowth.readList 13 185 ridgeSupport168_rest_006 =
    (ridgeSupport168_suffix_006, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 153
    ridgeSupport168_rest_006 ridgeSupport168_rest_007 ridgeSupport168_rest_012
    ridgeSupport168_006 ridgeSupport168_suffix_007 ridgeSupport168_006_decode ridgeSupport168_suffix_decode_007
theorem ridgeSupport168_suffix_decode_005 : PackedRawNatGrowth.readList 13 217 ridgeSupport168_rest_005 =
    (ridgeSupport168_suffix_005, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 185
    ridgeSupport168_rest_005 ridgeSupport168_rest_006 ridgeSupport168_rest_012
    ridgeSupport168_005 ridgeSupport168_suffix_006 ridgeSupport168_005_decode ridgeSupport168_suffix_decode_006
theorem ridgeSupport168_suffix_decode_004 : PackedRawNatGrowth.readList 13 249 ridgeSupport168_rest_004 =
    (ridgeSupport168_suffix_004, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 217
    ridgeSupport168_rest_004 ridgeSupport168_rest_005 ridgeSupport168_rest_012
    ridgeSupport168_004 ridgeSupport168_suffix_005 ridgeSupport168_004_decode ridgeSupport168_suffix_decode_005
theorem ridgeSupport168_suffix_decode_003 : PackedRawNatGrowth.readList 13 281 ridgeSupport168_rest_003 =
    (ridgeSupport168_suffix_003, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 249
    ridgeSupport168_rest_003 ridgeSupport168_rest_004 ridgeSupport168_rest_012
    ridgeSupport168_003 ridgeSupport168_suffix_004 ridgeSupport168_003_decode ridgeSupport168_suffix_decode_004
theorem ridgeSupport168_suffix_decode_002 : PackedRawNatGrowth.readList 13 313 ridgeSupport168_rest_002 =
    (ridgeSupport168_suffix_002, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 281
    ridgeSupport168_rest_002 ridgeSupport168_rest_003 ridgeSupport168_rest_012
    ridgeSupport168_002 ridgeSupport168_suffix_003 ridgeSupport168_002_decode ridgeSupport168_suffix_decode_003
theorem ridgeSupport168_suffix_decode_001 : PackedRawNatGrowth.readList 13 345 ridgeSupport168_rest_001 =
    (ridgeSupport168_suffix_001, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 313
    ridgeSupport168_rest_001 ridgeSupport168_rest_002 ridgeSupport168_rest_012
    ridgeSupport168_001 ridgeSupport168_suffix_002 ridgeSupport168_001_decode ridgeSupport168_suffix_decode_002
theorem ridgeSupport168_suffix_decode_000 : PackedRawNatGrowth.readList 13 377 ridgeSupport168_rest_000 =
    (ridgeSupport168_suffix_000, ridgeSupport168_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 345
    ridgeSupport168_rest_000 ridgeSupport168_rest_001 ridgeSupport168_rest_012
    ridgeSupport168_000 ridgeSupport168_suffix_001 ridgeSupport168_000_decode ridgeSupport168_suffix_decode_001
theorem ridgeSupport168_eq : candidateRows 168 = ridgeSupport168_suffix_000 := by
  change candidateSupports 168 = ridgeSupport168_suffix_000
  rw [ridgeSupport168_source]
  exact congrArg Prod.fst ridgeSupport168_suffix_decode_000
theorem ridgeTest_large_168 : ridgeTest 168 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport168_eq]
    simp only [ridgeSupport168_suffix_000, ridgeSupport168_suffix_001, ridgeSupport168_suffix_002, ridgeSupport168_suffix_003, ridgeSupport168_suffix_004, ridgeSupport168_suffix_005, ridgeSupport168_suffix_006, ridgeSupport168_suffix_007, ridgeSupport168_suffix_008, ridgeSupport168_suffix_009, ridgeSupport168_suffix_010, ridgeSupport168_suffix_011, ridgeSupport168_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport168_000_mask, ridgeSupport168_001_mask, ridgeSupport168_002_mask, ridgeSupport168_003_mask, ridgeSupport168_004_mask, ridgeSupport168_005_mask, ridgeSupport168_006_mask, ridgeSupport168_007_mask, ridgeSupport168_008_mask, ridgeSupport168_009_mask, ridgeSupport168_010_mask, ridgeSupport168_011_mask]
    decide +kernel
  · rw [ridgeSupport168_eq]
    simp only [ridgeSupport168_suffix_000, ridgeSupport168_suffix_001, ridgeSupport168_suffix_002, ridgeSupport168_suffix_003, ridgeSupport168_suffix_004, ridgeSupport168_suffix_005, ridgeSupport168_suffix_006, ridgeSupport168_suffix_007, ridgeSupport168_suffix_008, ridgeSupport168_suffix_009, ridgeSupport168_suffix_010, ridgeSupport168_suffix_011, ridgeSupport168_suffix_012, List.all_append, List.all_nil, ridgeSupport168_000_checked, ridgeSupport168_001_checked, ridgeSupport168_002_checked, ridgeSupport168_003_checked, ridgeSupport168_004_checked, ridgeSupport168_005_checked, ridgeSupport168_006_checked, ridgeSupport168_007_checked, ridgeSupport168_008_checked, ridgeSupport168_009_checked, ridgeSupport168_010_checked, ridgeSupport168_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
