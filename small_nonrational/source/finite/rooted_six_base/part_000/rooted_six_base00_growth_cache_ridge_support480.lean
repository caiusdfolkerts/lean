module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport480Part000
public import RootedSixBase00GrowthCacheRidgeSupport480Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport480_suffix_decode_010 : PackedRawNatGrowth.readList 15 0 ridgeSupport480_rest_010 =
    (ridgeSupport480_suffix_010, ridgeSupport480_rest_010) := by rfl
theorem ridgeSupport480_suffix_decode_009 : PackedRawNatGrowth.readList 15 3 ridgeSupport480_rest_009 =
    (ridgeSupport480_suffix_009, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport480_rest_009 ridgeSupport480_rest_010 ridgeSupport480_rest_010
    ridgeSupport480_009 ridgeSupport480_suffix_010 ridgeSupport480_009_decode ridgeSupport480_suffix_decode_010
theorem ridgeSupport480_suffix_decode_008 : PackedRawNatGrowth.readList 15 35 ridgeSupport480_rest_008 =
    (ridgeSupport480_suffix_008, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport480_rest_008 ridgeSupport480_rest_009 ridgeSupport480_rest_010
    ridgeSupport480_008 ridgeSupport480_suffix_009 ridgeSupport480_008_decode ridgeSupport480_suffix_decode_009
theorem ridgeSupport480_suffix_decode_007 : PackedRawNatGrowth.readList 15 67 ridgeSupport480_rest_007 =
    (ridgeSupport480_suffix_007, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport480_rest_007 ridgeSupport480_rest_008 ridgeSupport480_rest_010
    ridgeSupport480_007 ridgeSupport480_suffix_008 ridgeSupport480_007_decode ridgeSupport480_suffix_decode_008
theorem ridgeSupport480_suffix_decode_006 : PackedRawNatGrowth.readList 15 99 ridgeSupport480_rest_006 =
    (ridgeSupport480_suffix_006, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport480_rest_006 ridgeSupport480_rest_007 ridgeSupport480_rest_010
    ridgeSupport480_006 ridgeSupport480_suffix_007 ridgeSupport480_006_decode ridgeSupport480_suffix_decode_007
theorem ridgeSupport480_suffix_decode_005 : PackedRawNatGrowth.readList 15 131 ridgeSupport480_rest_005 =
    (ridgeSupport480_suffix_005, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport480_rest_005 ridgeSupport480_rest_006 ridgeSupport480_rest_010
    ridgeSupport480_005 ridgeSupport480_suffix_006 ridgeSupport480_005_decode ridgeSupport480_suffix_decode_006
theorem ridgeSupport480_suffix_decode_004 : PackedRawNatGrowth.readList 15 163 ridgeSupport480_rest_004 =
    (ridgeSupport480_suffix_004, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport480_rest_004 ridgeSupport480_rest_005 ridgeSupport480_rest_010
    ridgeSupport480_004 ridgeSupport480_suffix_005 ridgeSupport480_004_decode ridgeSupport480_suffix_decode_005
theorem ridgeSupport480_suffix_decode_003 : PackedRawNatGrowth.readList 15 195 ridgeSupport480_rest_003 =
    (ridgeSupport480_suffix_003, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport480_rest_003 ridgeSupport480_rest_004 ridgeSupport480_rest_010
    ridgeSupport480_003 ridgeSupport480_suffix_004 ridgeSupport480_003_decode ridgeSupport480_suffix_decode_004
theorem ridgeSupport480_suffix_decode_002 : PackedRawNatGrowth.readList 15 227 ridgeSupport480_rest_002 =
    (ridgeSupport480_suffix_002, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport480_rest_002 ridgeSupport480_rest_003 ridgeSupport480_rest_010
    ridgeSupport480_002 ridgeSupport480_suffix_003 ridgeSupport480_002_decode ridgeSupport480_suffix_decode_003
theorem ridgeSupport480_suffix_decode_001 : PackedRawNatGrowth.readList 15 259 ridgeSupport480_rest_001 =
    (ridgeSupport480_suffix_001, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport480_rest_001 ridgeSupport480_rest_002 ridgeSupport480_rest_010
    ridgeSupport480_001 ridgeSupport480_suffix_002 ridgeSupport480_001_decode ridgeSupport480_suffix_decode_002
theorem ridgeSupport480_suffix_decode_000 : PackedRawNatGrowth.readList 15 291 ridgeSupport480_rest_000 =
    (ridgeSupport480_suffix_000, ridgeSupport480_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport480_rest_000 ridgeSupport480_rest_001 ridgeSupport480_rest_010
    ridgeSupport480_000 ridgeSupport480_suffix_001 ridgeSupport480_000_decode ridgeSupport480_suffix_decode_001
theorem ridgeSupport480_eq : candidateRows 480 = ridgeSupport480_suffix_000 := by
  rw [ridgeSupport480_source]
  exact congrArg Prod.fst ridgeSupport480_suffix_decode_000
theorem ridgeTest_large_480 : ridgeTest 480 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport480_eq]
    simp only [ridgeSupport480_suffix_000, ridgeSupport480_suffix_001, ridgeSupport480_suffix_002, ridgeSupport480_suffix_003, ridgeSupport480_suffix_004, ridgeSupport480_suffix_005, ridgeSupport480_suffix_006, ridgeSupport480_suffix_007, ridgeSupport480_suffix_008, ridgeSupport480_suffix_009, ridgeSupport480_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport480_000_mask, ridgeSupport480_001_mask, ridgeSupport480_002_mask, ridgeSupport480_003_mask, ridgeSupport480_004_mask, ridgeSupport480_005_mask, ridgeSupport480_006_mask, ridgeSupport480_007_mask, ridgeSupport480_008_mask, ridgeSupport480_009_mask]
    decide +kernel
  · rw [ridgeSupport480_eq]
    simp only [ridgeSupport480_suffix_000, ridgeSupport480_suffix_001, ridgeSupport480_suffix_002, ridgeSupport480_suffix_003, ridgeSupport480_suffix_004, ridgeSupport480_suffix_005, ridgeSupport480_suffix_006, ridgeSupport480_suffix_007, ridgeSupport480_suffix_008, ridgeSupport480_suffix_009, ridgeSupport480_suffix_010, List.all_append, List.all_nil, ridgeSupport480_000_checked, ridgeSupport480_001_checked, ridgeSupport480_002_checked, ridgeSupport480_003_checked, ridgeSupport480_004_checked, ridgeSupport480_005_checked, ridgeSupport480_006_checked, ridgeSupport480_007_checked, ridgeSupport480_008_checked, ridgeSupport480_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
