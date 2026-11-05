module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport772Part000
public import RootedSixBase02GrowthCacheRidgeSupport772Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport772_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport772_rest_012 =
    (ridgeSupport772_suffix_012, ridgeSupport772_rest_012) := by rfl
theorem ridgeSupport772_suffix_decode_011 : PackedRawNatGrowth.readList 13 3 ridgeSupport772_rest_011 =
    (ridgeSupport772_suffix_011, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 3 0
    ridgeSupport772_rest_011 ridgeSupport772_rest_012 ridgeSupport772_rest_012
    ridgeSupport772_011 ridgeSupport772_suffix_012 ridgeSupport772_011_decode ridgeSupport772_suffix_decode_012
theorem ridgeSupport772_suffix_decode_010 : PackedRawNatGrowth.readList 13 35 ridgeSupport772_rest_010 =
    (ridgeSupport772_suffix_010, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3
    ridgeSupport772_rest_010 ridgeSupport772_rest_011 ridgeSupport772_rest_012
    ridgeSupport772_010 ridgeSupport772_suffix_011 ridgeSupport772_010_decode ridgeSupport772_suffix_decode_011
theorem ridgeSupport772_suffix_decode_009 : PackedRawNatGrowth.readList 13 67 ridgeSupport772_rest_009 =
    (ridgeSupport772_suffix_009, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 35
    ridgeSupport772_rest_009 ridgeSupport772_rest_010 ridgeSupport772_rest_012
    ridgeSupport772_009 ridgeSupport772_suffix_010 ridgeSupport772_009_decode ridgeSupport772_suffix_decode_010
theorem ridgeSupport772_suffix_decode_008 : PackedRawNatGrowth.readList 13 99 ridgeSupport772_rest_008 =
    (ridgeSupport772_suffix_008, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 67
    ridgeSupport772_rest_008 ridgeSupport772_rest_009 ridgeSupport772_rest_012
    ridgeSupport772_008 ridgeSupport772_suffix_009 ridgeSupport772_008_decode ridgeSupport772_suffix_decode_009
theorem ridgeSupport772_suffix_decode_007 : PackedRawNatGrowth.readList 13 131 ridgeSupport772_rest_007 =
    (ridgeSupport772_suffix_007, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 99
    ridgeSupport772_rest_007 ridgeSupport772_rest_008 ridgeSupport772_rest_012
    ridgeSupport772_007 ridgeSupport772_suffix_008 ridgeSupport772_007_decode ridgeSupport772_suffix_decode_008
theorem ridgeSupport772_suffix_decode_006 : PackedRawNatGrowth.readList 13 163 ridgeSupport772_rest_006 =
    (ridgeSupport772_suffix_006, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 131
    ridgeSupport772_rest_006 ridgeSupport772_rest_007 ridgeSupport772_rest_012
    ridgeSupport772_006 ridgeSupport772_suffix_007 ridgeSupport772_006_decode ridgeSupport772_suffix_decode_007
theorem ridgeSupport772_suffix_decode_005 : PackedRawNatGrowth.readList 13 195 ridgeSupport772_rest_005 =
    (ridgeSupport772_suffix_005, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 163
    ridgeSupport772_rest_005 ridgeSupport772_rest_006 ridgeSupport772_rest_012
    ridgeSupport772_005 ridgeSupport772_suffix_006 ridgeSupport772_005_decode ridgeSupport772_suffix_decode_006
theorem ridgeSupport772_suffix_decode_004 : PackedRawNatGrowth.readList 13 227 ridgeSupport772_rest_004 =
    (ridgeSupport772_suffix_004, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 195
    ridgeSupport772_rest_004 ridgeSupport772_rest_005 ridgeSupport772_rest_012
    ridgeSupport772_004 ridgeSupport772_suffix_005 ridgeSupport772_004_decode ridgeSupport772_suffix_decode_005
theorem ridgeSupport772_suffix_decode_003 : PackedRawNatGrowth.readList 13 259 ridgeSupport772_rest_003 =
    (ridgeSupport772_suffix_003, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 227
    ridgeSupport772_rest_003 ridgeSupport772_rest_004 ridgeSupport772_rest_012
    ridgeSupport772_003 ridgeSupport772_suffix_004 ridgeSupport772_003_decode ridgeSupport772_suffix_decode_004
theorem ridgeSupport772_suffix_decode_002 : PackedRawNatGrowth.readList 13 291 ridgeSupport772_rest_002 =
    (ridgeSupport772_suffix_002, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 259
    ridgeSupport772_rest_002 ridgeSupport772_rest_003 ridgeSupport772_rest_012
    ridgeSupport772_002 ridgeSupport772_suffix_003 ridgeSupport772_002_decode ridgeSupport772_suffix_decode_003
theorem ridgeSupport772_suffix_decode_001 : PackedRawNatGrowth.readList 13 323 ridgeSupport772_rest_001 =
    (ridgeSupport772_suffix_001, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 291
    ridgeSupport772_rest_001 ridgeSupport772_rest_002 ridgeSupport772_rest_012
    ridgeSupport772_001 ridgeSupport772_suffix_002 ridgeSupport772_001_decode ridgeSupport772_suffix_decode_002
theorem ridgeSupport772_suffix_decode_000 : PackedRawNatGrowth.readList 13 355 ridgeSupport772_rest_000 =
    (ridgeSupport772_suffix_000, ridgeSupport772_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 323
    ridgeSupport772_rest_000 ridgeSupport772_rest_001 ridgeSupport772_rest_012
    ridgeSupport772_000 ridgeSupport772_suffix_001 ridgeSupport772_000_decode ridgeSupport772_suffix_decode_001
theorem ridgeSupport772_eq : candidateRows 772 = ridgeSupport772_suffix_000 := by
  change candidateSupports 772 = ridgeSupport772_suffix_000
  rw [ridgeSupport772_source]
  exact congrArg Prod.fst ridgeSupport772_suffix_decode_000
theorem ridgeTest_large_772 : ridgeTest 772 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, ridgeSupport772_suffix_010, ridgeSupport772_suffix_011, ridgeSupport772_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport772_000_mask, ridgeSupport772_001_mask, ridgeSupport772_002_mask, ridgeSupport772_003_mask, ridgeSupport772_004_mask, ridgeSupport772_005_mask, ridgeSupport772_006_mask, ridgeSupport772_007_mask, ridgeSupport772_008_mask, ridgeSupport772_009_mask, ridgeSupport772_010_mask, ridgeSupport772_011_mask]
    decide +kernel
  · rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, ridgeSupport772_suffix_010, ridgeSupport772_suffix_011, ridgeSupport772_suffix_012, List.all_append, List.all_nil, ridgeSupport772_000_checked, ridgeSupport772_001_checked, ridgeSupport772_002_checked, ridgeSupport772_003_checked, ridgeSupport772_004_checked, ridgeSupport772_005_checked, ridgeSupport772_006_checked, ridgeSupport772_007_checked, ridgeSupport772_008_checked, ridgeSupport772_009_checked, ridgeSupport772_010_checked, ridgeSupport772_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
