module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport897Part000
public import RootedSixBase00GrowthCacheRidgeSupport897Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport897_suffix_decode_010 : PackedRawNatGrowth.readList 15 0 ridgeSupport897_rest_010 =
    (ridgeSupport897_suffix_010, ridgeSupport897_rest_010) := by rfl
theorem ridgeSupport897_suffix_decode_009 : PackedRawNatGrowth.readList 15 3 ridgeSupport897_rest_009 =
    (ridgeSupport897_suffix_009, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport897_rest_009 ridgeSupport897_rest_010 ridgeSupport897_rest_010
    ridgeSupport897_009 ridgeSupport897_suffix_010 ridgeSupport897_009_decode ridgeSupport897_suffix_decode_010
theorem ridgeSupport897_suffix_decode_008 : PackedRawNatGrowth.readList 15 35 ridgeSupport897_rest_008 =
    (ridgeSupport897_suffix_008, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport897_rest_008 ridgeSupport897_rest_009 ridgeSupport897_rest_010
    ridgeSupport897_008 ridgeSupport897_suffix_009 ridgeSupport897_008_decode ridgeSupport897_suffix_decode_009
theorem ridgeSupport897_suffix_decode_007 : PackedRawNatGrowth.readList 15 67 ridgeSupport897_rest_007 =
    (ridgeSupport897_suffix_007, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport897_rest_007 ridgeSupport897_rest_008 ridgeSupport897_rest_010
    ridgeSupport897_007 ridgeSupport897_suffix_008 ridgeSupport897_007_decode ridgeSupport897_suffix_decode_008
theorem ridgeSupport897_suffix_decode_006 : PackedRawNatGrowth.readList 15 99 ridgeSupport897_rest_006 =
    (ridgeSupport897_suffix_006, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport897_rest_006 ridgeSupport897_rest_007 ridgeSupport897_rest_010
    ridgeSupport897_006 ridgeSupport897_suffix_007 ridgeSupport897_006_decode ridgeSupport897_suffix_decode_007
theorem ridgeSupport897_suffix_decode_005 : PackedRawNatGrowth.readList 15 131 ridgeSupport897_rest_005 =
    (ridgeSupport897_suffix_005, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport897_rest_005 ridgeSupport897_rest_006 ridgeSupport897_rest_010
    ridgeSupport897_005 ridgeSupport897_suffix_006 ridgeSupport897_005_decode ridgeSupport897_suffix_decode_006
theorem ridgeSupport897_suffix_decode_004 : PackedRawNatGrowth.readList 15 163 ridgeSupport897_rest_004 =
    (ridgeSupport897_suffix_004, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport897_rest_004 ridgeSupport897_rest_005 ridgeSupport897_rest_010
    ridgeSupport897_004 ridgeSupport897_suffix_005 ridgeSupport897_004_decode ridgeSupport897_suffix_decode_005
theorem ridgeSupport897_suffix_decode_003 : PackedRawNatGrowth.readList 15 195 ridgeSupport897_rest_003 =
    (ridgeSupport897_suffix_003, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport897_rest_003 ridgeSupport897_rest_004 ridgeSupport897_rest_010
    ridgeSupport897_003 ridgeSupport897_suffix_004 ridgeSupport897_003_decode ridgeSupport897_suffix_decode_004
theorem ridgeSupport897_suffix_decode_002 : PackedRawNatGrowth.readList 15 227 ridgeSupport897_rest_002 =
    (ridgeSupport897_suffix_002, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport897_rest_002 ridgeSupport897_rest_003 ridgeSupport897_rest_010
    ridgeSupport897_002 ridgeSupport897_suffix_003 ridgeSupport897_002_decode ridgeSupport897_suffix_decode_003
theorem ridgeSupport897_suffix_decode_001 : PackedRawNatGrowth.readList 15 259 ridgeSupport897_rest_001 =
    (ridgeSupport897_suffix_001, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport897_rest_001 ridgeSupport897_rest_002 ridgeSupport897_rest_010
    ridgeSupport897_001 ridgeSupport897_suffix_002 ridgeSupport897_001_decode ridgeSupport897_suffix_decode_002
theorem ridgeSupport897_suffix_decode_000 : PackedRawNatGrowth.readList 15 291 ridgeSupport897_rest_000 =
    (ridgeSupport897_suffix_000, ridgeSupport897_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport897_rest_000 ridgeSupport897_rest_001 ridgeSupport897_rest_010
    ridgeSupport897_000 ridgeSupport897_suffix_001 ridgeSupport897_000_decode ridgeSupport897_suffix_decode_001
theorem ridgeSupport897_eq : candidateRows 897 = ridgeSupport897_suffix_000 := by
  rw [ridgeSupport897_source]
  exact congrArg Prod.fst ridgeSupport897_suffix_decode_000
theorem ridgeTest_large_897 : ridgeTest 897 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport897_eq]
    simp only [ridgeSupport897_suffix_000, ridgeSupport897_suffix_001, ridgeSupport897_suffix_002, ridgeSupport897_suffix_003, ridgeSupport897_suffix_004, ridgeSupport897_suffix_005, ridgeSupport897_suffix_006, ridgeSupport897_suffix_007, ridgeSupport897_suffix_008, ridgeSupport897_suffix_009, ridgeSupport897_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport897_000_mask, ridgeSupport897_001_mask, ridgeSupport897_002_mask, ridgeSupport897_003_mask, ridgeSupport897_004_mask, ridgeSupport897_005_mask, ridgeSupport897_006_mask, ridgeSupport897_007_mask, ridgeSupport897_008_mask, ridgeSupport897_009_mask]
    decide +kernel
  · rw [ridgeSupport897_eq]
    simp only [ridgeSupport897_suffix_000, ridgeSupport897_suffix_001, ridgeSupport897_suffix_002, ridgeSupport897_suffix_003, ridgeSupport897_suffix_004, ridgeSupport897_suffix_005, ridgeSupport897_suffix_006, ridgeSupport897_suffix_007, ridgeSupport897_suffix_008, ridgeSupport897_suffix_009, ridgeSupport897_suffix_010, List.all_append, List.all_nil, ridgeSupport897_000_checked, ridgeSupport897_001_checked, ridgeSupport897_002_checked, ridgeSupport897_003_checked, ridgeSupport897_004_checked, ridgeSupport897_005_checked, ridgeSupport897_006_checked, ridgeSupport897_007_checked, ridgeSupport897_008_checked, ridgeSupport897_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
