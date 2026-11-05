module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport450Part000
public import RootedSixBase00GrowthCacheRidgeSupport450Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport450_suffix_decode_013 : PackedRawNatGrowth.readList 15 0 ridgeSupport450_rest_013 =
    (ridgeSupport450_suffix_013, ridgeSupport450_rest_013) := by rfl
theorem ridgeSupport450_suffix_decode_012 : PackedRawNatGrowth.readList 15 3 ridgeSupport450_rest_012 =
    (ridgeSupport450_suffix_012, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport450_rest_012 ridgeSupport450_rest_013 ridgeSupport450_rest_013
    ridgeSupport450_012 ridgeSupport450_suffix_013 ridgeSupport450_012_decode ridgeSupport450_suffix_decode_013
theorem ridgeSupport450_suffix_decode_011 : PackedRawNatGrowth.readList 15 35 ridgeSupport450_rest_011 =
    (ridgeSupport450_suffix_011, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport450_rest_011 ridgeSupport450_rest_012 ridgeSupport450_rest_013
    ridgeSupport450_011 ridgeSupport450_suffix_012 ridgeSupport450_011_decode ridgeSupport450_suffix_decode_012
theorem ridgeSupport450_suffix_decode_010 : PackedRawNatGrowth.readList 15 67 ridgeSupport450_rest_010 =
    (ridgeSupport450_suffix_010, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport450_rest_010 ridgeSupport450_rest_011 ridgeSupport450_rest_013
    ridgeSupport450_010 ridgeSupport450_suffix_011 ridgeSupport450_010_decode ridgeSupport450_suffix_decode_011
theorem ridgeSupport450_suffix_decode_009 : PackedRawNatGrowth.readList 15 99 ridgeSupport450_rest_009 =
    (ridgeSupport450_suffix_009, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport450_rest_009 ridgeSupport450_rest_010 ridgeSupport450_rest_013
    ridgeSupport450_009 ridgeSupport450_suffix_010 ridgeSupport450_009_decode ridgeSupport450_suffix_decode_010
theorem ridgeSupport450_suffix_decode_008 : PackedRawNatGrowth.readList 15 131 ridgeSupport450_rest_008 =
    (ridgeSupport450_suffix_008, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport450_rest_008 ridgeSupport450_rest_009 ridgeSupport450_rest_013
    ridgeSupport450_008 ridgeSupport450_suffix_009 ridgeSupport450_008_decode ridgeSupport450_suffix_decode_009
theorem ridgeSupport450_suffix_decode_007 : PackedRawNatGrowth.readList 15 163 ridgeSupport450_rest_007 =
    (ridgeSupport450_suffix_007, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport450_rest_007 ridgeSupport450_rest_008 ridgeSupport450_rest_013
    ridgeSupport450_007 ridgeSupport450_suffix_008 ridgeSupport450_007_decode ridgeSupport450_suffix_decode_008
theorem ridgeSupport450_suffix_decode_006 : PackedRawNatGrowth.readList 15 195 ridgeSupport450_rest_006 =
    (ridgeSupport450_suffix_006, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport450_rest_006 ridgeSupport450_rest_007 ridgeSupport450_rest_013
    ridgeSupport450_006 ridgeSupport450_suffix_007 ridgeSupport450_006_decode ridgeSupport450_suffix_decode_007
theorem ridgeSupport450_suffix_decode_005 : PackedRawNatGrowth.readList 15 227 ridgeSupport450_rest_005 =
    (ridgeSupport450_suffix_005, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport450_rest_005 ridgeSupport450_rest_006 ridgeSupport450_rest_013
    ridgeSupport450_005 ridgeSupport450_suffix_006 ridgeSupport450_005_decode ridgeSupport450_suffix_decode_006
theorem ridgeSupport450_suffix_decode_004 : PackedRawNatGrowth.readList 15 259 ridgeSupport450_rest_004 =
    (ridgeSupport450_suffix_004, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport450_rest_004 ridgeSupport450_rest_005 ridgeSupport450_rest_013
    ridgeSupport450_004 ridgeSupport450_suffix_005 ridgeSupport450_004_decode ridgeSupport450_suffix_decode_005
theorem ridgeSupport450_suffix_decode_003 : PackedRawNatGrowth.readList 15 291 ridgeSupport450_rest_003 =
    (ridgeSupport450_suffix_003, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport450_rest_003 ridgeSupport450_rest_004 ridgeSupport450_rest_013
    ridgeSupport450_003 ridgeSupport450_suffix_004 ridgeSupport450_003_decode ridgeSupport450_suffix_decode_004
theorem ridgeSupport450_suffix_decode_002 : PackedRawNatGrowth.readList 15 323 ridgeSupport450_rest_002 =
    (ridgeSupport450_suffix_002, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport450_rest_002 ridgeSupport450_rest_003 ridgeSupport450_rest_013
    ridgeSupport450_002 ridgeSupport450_suffix_003 ridgeSupport450_002_decode ridgeSupport450_suffix_decode_003
theorem ridgeSupport450_suffix_decode_001 : PackedRawNatGrowth.readList 15 355 ridgeSupport450_rest_001 =
    (ridgeSupport450_suffix_001, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport450_rest_001 ridgeSupport450_rest_002 ridgeSupport450_rest_013
    ridgeSupport450_001 ridgeSupport450_suffix_002 ridgeSupport450_001_decode ridgeSupport450_suffix_decode_002
theorem ridgeSupport450_suffix_decode_000 : PackedRawNatGrowth.readList 15 387 ridgeSupport450_rest_000 =
    (ridgeSupport450_suffix_000, ridgeSupport450_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport450_rest_000 ridgeSupport450_rest_001 ridgeSupport450_rest_013
    ridgeSupport450_000 ridgeSupport450_suffix_001 ridgeSupport450_000_decode ridgeSupport450_suffix_decode_001
theorem ridgeSupport450_eq : candidateRows 450 = ridgeSupport450_suffix_000 := by
  rw [ridgeSupport450_source]
  exact congrArg Prod.fst ridgeSupport450_suffix_decode_000
theorem ridgeTest_large_450 : ridgeTest 450 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport450_eq]
    simp only [ridgeSupport450_suffix_000, ridgeSupport450_suffix_001, ridgeSupport450_suffix_002, ridgeSupport450_suffix_003, ridgeSupport450_suffix_004, ridgeSupport450_suffix_005, ridgeSupport450_suffix_006, ridgeSupport450_suffix_007, ridgeSupport450_suffix_008, ridgeSupport450_suffix_009, ridgeSupport450_suffix_010, ridgeSupport450_suffix_011, ridgeSupport450_suffix_012, ridgeSupport450_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport450_000_mask, ridgeSupport450_001_mask, ridgeSupport450_002_mask, ridgeSupport450_003_mask, ridgeSupport450_004_mask, ridgeSupport450_005_mask, ridgeSupport450_006_mask, ridgeSupport450_007_mask, ridgeSupport450_008_mask, ridgeSupport450_009_mask, ridgeSupport450_010_mask, ridgeSupport450_011_mask, ridgeSupport450_012_mask]
    decide +kernel
  · rw [ridgeSupport450_eq]
    simp only [ridgeSupport450_suffix_000, ridgeSupport450_suffix_001, ridgeSupport450_suffix_002, ridgeSupport450_suffix_003, ridgeSupport450_suffix_004, ridgeSupport450_suffix_005, ridgeSupport450_suffix_006, ridgeSupport450_suffix_007, ridgeSupport450_suffix_008, ridgeSupport450_suffix_009, ridgeSupport450_suffix_010, ridgeSupport450_suffix_011, ridgeSupport450_suffix_012, ridgeSupport450_suffix_013, List.all_append, List.all_nil, ridgeSupport450_000_checked, ridgeSupport450_001_checked, ridgeSupport450_002_checked, ridgeSupport450_003_checked, ridgeSupport450_004_checked, ridgeSupport450_005_checked, ridgeSupport450_006_checked, ridgeSupport450_007_checked, ridgeSupport450_008_checked, ridgeSupport450_009_checked, ridgeSupport450_010_checked, ridgeSupport450_011_checked, ridgeSupport450_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
