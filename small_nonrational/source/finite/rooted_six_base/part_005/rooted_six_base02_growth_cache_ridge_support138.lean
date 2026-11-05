module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport138Part000
public import RootedSixBase02GrowthCacheRidgeSupport138Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport138_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport138_rest_012 =
    (ridgeSupport138_suffix_012, ridgeSupport138_rest_012) := by rfl
theorem ridgeSupport138_suffix_decode_011 : PackedRawNatGrowth.readList 13 25 ridgeSupport138_rest_011 =
    (ridgeSupport138_suffix_011, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 25 0
    ridgeSupport138_rest_011 ridgeSupport138_rest_012 ridgeSupport138_rest_012
    ridgeSupport138_011 ridgeSupport138_suffix_012 ridgeSupport138_011_decode ridgeSupport138_suffix_decode_012
theorem ridgeSupport138_suffix_decode_010 : PackedRawNatGrowth.readList 13 57 ridgeSupport138_rest_010 =
    (ridgeSupport138_suffix_010, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 25
    ridgeSupport138_rest_010 ridgeSupport138_rest_011 ridgeSupport138_rest_012
    ridgeSupport138_010 ridgeSupport138_suffix_011 ridgeSupport138_010_decode ridgeSupport138_suffix_decode_011
theorem ridgeSupport138_suffix_decode_009 : PackedRawNatGrowth.readList 13 89 ridgeSupport138_rest_009 =
    (ridgeSupport138_suffix_009, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 57
    ridgeSupport138_rest_009 ridgeSupport138_rest_010 ridgeSupport138_rest_012
    ridgeSupport138_009 ridgeSupport138_suffix_010 ridgeSupport138_009_decode ridgeSupport138_suffix_decode_010
theorem ridgeSupport138_suffix_decode_008 : PackedRawNatGrowth.readList 13 121 ridgeSupport138_rest_008 =
    (ridgeSupport138_suffix_008, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 89
    ridgeSupport138_rest_008 ridgeSupport138_rest_009 ridgeSupport138_rest_012
    ridgeSupport138_008 ridgeSupport138_suffix_009 ridgeSupport138_008_decode ridgeSupport138_suffix_decode_009
theorem ridgeSupport138_suffix_decode_007 : PackedRawNatGrowth.readList 13 153 ridgeSupport138_rest_007 =
    (ridgeSupport138_suffix_007, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 121
    ridgeSupport138_rest_007 ridgeSupport138_rest_008 ridgeSupport138_rest_012
    ridgeSupport138_007 ridgeSupport138_suffix_008 ridgeSupport138_007_decode ridgeSupport138_suffix_decode_008
theorem ridgeSupport138_suffix_decode_006 : PackedRawNatGrowth.readList 13 185 ridgeSupport138_rest_006 =
    (ridgeSupport138_suffix_006, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 153
    ridgeSupport138_rest_006 ridgeSupport138_rest_007 ridgeSupport138_rest_012
    ridgeSupport138_006 ridgeSupport138_suffix_007 ridgeSupport138_006_decode ridgeSupport138_suffix_decode_007
theorem ridgeSupport138_suffix_decode_005 : PackedRawNatGrowth.readList 13 217 ridgeSupport138_rest_005 =
    (ridgeSupport138_suffix_005, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 185
    ridgeSupport138_rest_005 ridgeSupport138_rest_006 ridgeSupport138_rest_012
    ridgeSupport138_005 ridgeSupport138_suffix_006 ridgeSupport138_005_decode ridgeSupport138_suffix_decode_006
theorem ridgeSupport138_suffix_decode_004 : PackedRawNatGrowth.readList 13 249 ridgeSupport138_rest_004 =
    (ridgeSupport138_suffix_004, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 217
    ridgeSupport138_rest_004 ridgeSupport138_rest_005 ridgeSupport138_rest_012
    ridgeSupport138_004 ridgeSupport138_suffix_005 ridgeSupport138_004_decode ridgeSupport138_suffix_decode_005
theorem ridgeSupport138_suffix_decode_003 : PackedRawNatGrowth.readList 13 281 ridgeSupport138_rest_003 =
    (ridgeSupport138_suffix_003, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 249
    ridgeSupport138_rest_003 ridgeSupport138_rest_004 ridgeSupport138_rest_012
    ridgeSupport138_003 ridgeSupport138_suffix_004 ridgeSupport138_003_decode ridgeSupport138_suffix_decode_004
theorem ridgeSupport138_suffix_decode_002 : PackedRawNatGrowth.readList 13 313 ridgeSupport138_rest_002 =
    (ridgeSupport138_suffix_002, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 281
    ridgeSupport138_rest_002 ridgeSupport138_rest_003 ridgeSupport138_rest_012
    ridgeSupport138_002 ridgeSupport138_suffix_003 ridgeSupport138_002_decode ridgeSupport138_suffix_decode_003
theorem ridgeSupport138_suffix_decode_001 : PackedRawNatGrowth.readList 13 345 ridgeSupport138_rest_001 =
    (ridgeSupport138_suffix_001, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 313
    ridgeSupport138_rest_001 ridgeSupport138_rest_002 ridgeSupport138_rest_012
    ridgeSupport138_001 ridgeSupport138_suffix_002 ridgeSupport138_001_decode ridgeSupport138_suffix_decode_002
theorem ridgeSupport138_suffix_decode_000 : PackedRawNatGrowth.readList 13 377 ridgeSupport138_rest_000 =
    (ridgeSupport138_suffix_000, ridgeSupport138_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 345
    ridgeSupport138_rest_000 ridgeSupport138_rest_001 ridgeSupport138_rest_012
    ridgeSupport138_000 ridgeSupport138_suffix_001 ridgeSupport138_000_decode ridgeSupport138_suffix_decode_001
theorem ridgeSupport138_eq : candidateRows 138 = ridgeSupport138_suffix_000 := by
  change candidateSupports 138 = ridgeSupport138_suffix_000
  rw [ridgeSupport138_source]
  exact congrArg Prod.fst ridgeSupport138_suffix_decode_000
theorem ridgeTest_large_138 : ridgeTest 138 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport138_eq]
    simp only [ridgeSupport138_suffix_000, ridgeSupport138_suffix_001, ridgeSupport138_suffix_002, ridgeSupport138_suffix_003, ridgeSupport138_suffix_004, ridgeSupport138_suffix_005, ridgeSupport138_suffix_006, ridgeSupport138_suffix_007, ridgeSupport138_suffix_008, ridgeSupport138_suffix_009, ridgeSupport138_suffix_010, ridgeSupport138_suffix_011, ridgeSupport138_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport138_000_mask, ridgeSupport138_001_mask, ridgeSupport138_002_mask, ridgeSupport138_003_mask, ridgeSupport138_004_mask, ridgeSupport138_005_mask, ridgeSupport138_006_mask, ridgeSupport138_007_mask, ridgeSupport138_008_mask, ridgeSupport138_009_mask, ridgeSupport138_010_mask, ridgeSupport138_011_mask]
    decide +kernel
  · rw [ridgeSupport138_eq]
    simp only [ridgeSupport138_suffix_000, ridgeSupport138_suffix_001, ridgeSupport138_suffix_002, ridgeSupport138_suffix_003, ridgeSupport138_suffix_004, ridgeSupport138_suffix_005, ridgeSupport138_suffix_006, ridgeSupport138_suffix_007, ridgeSupport138_suffix_008, ridgeSupport138_suffix_009, ridgeSupport138_suffix_010, ridgeSupport138_suffix_011, ridgeSupport138_suffix_012, List.all_append, List.all_nil, ridgeSupport138_000_checked, ridgeSupport138_001_checked, ridgeSupport138_002_checked, ridgeSupport138_003_checked, ridgeSupport138_004_checked, ridgeSupport138_005_checked, ridgeSupport138_006_checked, ridgeSupport138_007_checked, ridgeSupport138_008_checked, ridgeSupport138_009_checked, ridgeSupport138_010_checked, ridgeSupport138_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
