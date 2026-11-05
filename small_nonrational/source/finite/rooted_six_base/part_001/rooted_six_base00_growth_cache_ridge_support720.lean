module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport720Part000
public import RootedSixBase00GrowthCacheRidgeSupport720Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport720_suffix_decode_013 : PackedRawNatGrowth.readList 15 0 ridgeSupport720_rest_013 =
    (ridgeSupport720_suffix_013, ridgeSupport720_rest_013) := by rfl
theorem ridgeSupport720_suffix_decode_012 : PackedRawNatGrowth.readList 15 3 ridgeSupport720_rest_012 =
    (ridgeSupport720_suffix_012, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport720_rest_012 ridgeSupport720_rest_013 ridgeSupport720_rest_013
    ridgeSupport720_012 ridgeSupport720_suffix_013 ridgeSupport720_012_decode ridgeSupport720_suffix_decode_013
theorem ridgeSupport720_suffix_decode_011 : PackedRawNatGrowth.readList 15 35 ridgeSupport720_rest_011 =
    (ridgeSupport720_suffix_011, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport720_rest_011 ridgeSupport720_rest_012 ridgeSupport720_rest_013
    ridgeSupport720_011 ridgeSupport720_suffix_012 ridgeSupport720_011_decode ridgeSupport720_suffix_decode_012
theorem ridgeSupport720_suffix_decode_010 : PackedRawNatGrowth.readList 15 67 ridgeSupport720_rest_010 =
    (ridgeSupport720_suffix_010, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport720_rest_010 ridgeSupport720_rest_011 ridgeSupport720_rest_013
    ridgeSupport720_010 ridgeSupport720_suffix_011 ridgeSupport720_010_decode ridgeSupport720_suffix_decode_011
theorem ridgeSupport720_suffix_decode_009 : PackedRawNatGrowth.readList 15 99 ridgeSupport720_rest_009 =
    (ridgeSupport720_suffix_009, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport720_rest_009 ridgeSupport720_rest_010 ridgeSupport720_rest_013
    ridgeSupport720_009 ridgeSupport720_suffix_010 ridgeSupport720_009_decode ridgeSupport720_suffix_decode_010
theorem ridgeSupport720_suffix_decode_008 : PackedRawNatGrowth.readList 15 131 ridgeSupport720_rest_008 =
    (ridgeSupport720_suffix_008, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport720_rest_008 ridgeSupport720_rest_009 ridgeSupport720_rest_013
    ridgeSupport720_008 ridgeSupport720_suffix_009 ridgeSupport720_008_decode ridgeSupport720_suffix_decode_009
theorem ridgeSupport720_suffix_decode_007 : PackedRawNatGrowth.readList 15 163 ridgeSupport720_rest_007 =
    (ridgeSupport720_suffix_007, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport720_rest_007 ridgeSupport720_rest_008 ridgeSupport720_rest_013
    ridgeSupport720_007 ridgeSupport720_suffix_008 ridgeSupport720_007_decode ridgeSupport720_suffix_decode_008
theorem ridgeSupport720_suffix_decode_006 : PackedRawNatGrowth.readList 15 195 ridgeSupport720_rest_006 =
    (ridgeSupport720_suffix_006, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport720_rest_006 ridgeSupport720_rest_007 ridgeSupport720_rest_013
    ridgeSupport720_006 ridgeSupport720_suffix_007 ridgeSupport720_006_decode ridgeSupport720_suffix_decode_007
theorem ridgeSupport720_suffix_decode_005 : PackedRawNatGrowth.readList 15 227 ridgeSupport720_rest_005 =
    (ridgeSupport720_suffix_005, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport720_rest_005 ridgeSupport720_rest_006 ridgeSupport720_rest_013
    ridgeSupport720_005 ridgeSupport720_suffix_006 ridgeSupport720_005_decode ridgeSupport720_suffix_decode_006
theorem ridgeSupport720_suffix_decode_004 : PackedRawNatGrowth.readList 15 259 ridgeSupport720_rest_004 =
    (ridgeSupport720_suffix_004, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport720_rest_004 ridgeSupport720_rest_005 ridgeSupport720_rest_013
    ridgeSupport720_004 ridgeSupport720_suffix_005 ridgeSupport720_004_decode ridgeSupport720_suffix_decode_005
theorem ridgeSupport720_suffix_decode_003 : PackedRawNatGrowth.readList 15 291 ridgeSupport720_rest_003 =
    (ridgeSupport720_suffix_003, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport720_rest_003 ridgeSupport720_rest_004 ridgeSupport720_rest_013
    ridgeSupport720_003 ridgeSupport720_suffix_004 ridgeSupport720_003_decode ridgeSupport720_suffix_decode_004
theorem ridgeSupport720_suffix_decode_002 : PackedRawNatGrowth.readList 15 323 ridgeSupport720_rest_002 =
    (ridgeSupport720_suffix_002, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport720_rest_002 ridgeSupport720_rest_003 ridgeSupport720_rest_013
    ridgeSupport720_002 ridgeSupport720_suffix_003 ridgeSupport720_002_decode ridgeSupport720_suffix_decode_003
theorem ridgeSupport720_suffix_decode_001 : PackedRawNatGrowth.readList 15 355 ridgeSupport720_rest_001 =
    (ridgeSupport720_suffix_001, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport720_rest_001 ridgeSupport720_rest_002 ridgeSupport720_rest_013
    ridgeSupport720_001 ridgeSupport720_suffix_002 ridgeSupport720_001_decode ridgeSupport720_suffix_decode_002
theorem ridgeSupport720_suffix_decode_000 : PackedRawNatGrowth.readList 15 387 ridgeSupport720_rest_000 =
    (ridgeSupport720_suffix_000, ridgeSupport720_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport720_rest_000 ridgeSupport720_rest_001 ridgeSupport720_rest_013
    ridgeSupport720_000 ridgeSupport720_suffix_001 ridgeSupport720_000_decode ridgeSupport720_suffix_decode_001
theorem ridgeSupport720_eq : candidateRows 720 = ridgeSupport720_suffix_000 := by
  rw [ridgeSupport720_source]
  exact congrArg Prod.fst ridgeSupport720_suffix_decode_000
theorem ridgeTest_large_720 : ridgeTest 720 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport720_eq]
    simp only [ridgeSupport720_suffix_000, ridgeSupport720_suffix_001, ridgeSupport720_suffix_002, ridgeSupport720_suffix_003, ridgeSupport720_suffix_004, ridgeSupport720_suffix_005, ridgeSupport720_suffix_006, ridgeSupport720_suffix_007, ridgeSupport720_suffix_008, ridgeSupport720_suffix_009, ridgeSupport720_suffix_010, ridgeSupport720_suffix_011, ridgeSupport720_suffix_012, ridgeSupport720_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport720_000_mask, ridgeSupport720_001_mask, ridgeSupport720_002_mask, ridgeSupport720_003_mask, ridgeSupport720_004_mask, ridgeSupport720_005_mask, ridgeSupport720_006_mask, ridgeSupport720_007_mask, ridgeSupport720_008_mask, ridgeSupport720_009_mask, ridgeSupport720_010_mask, ridgeSupport720_011_mask, ridgeSupport720_012_mask]
    decide +kernel
  · rw [ridgeSupport720_eq]
    simp only [ridgeSupport720_suffix_000, ridgeSupport720_suffix_001, ridgeSupport720_suffix_002, ridgeSupport720_suffix_003, ridgeSupport720_suffix_004, ridgeSupport720_suffix_005, ridgeSupport720_suffix_006, ridgeSupport720_suffix_007, ridgeSupport720_suffix_008, ridgeSupport720_suffix_009, ridgeSupport720_suffix_010, ridgeSupport720_suffix_011, ridgeSupport720_suffix_012, ridgeSupport720_suffix_013, List.all_append, List.all_nil, ridgeSupport720_000_checked, ridgeSupport720_001_checked, ridgeSupport720_002_checked, ridgeSupport720_003_checked, ridgeSupport720_004_checked, ridgeSupport720_005_checked, ridgeSupport720_006_checked, ridgeSupport720_007_checked, ridgeSupport720_008_checked, ridgeSupport720_009_checked, ridgeSupport720_010_checked, ridgeSupport720_011_checked, ridgeSupport720_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
