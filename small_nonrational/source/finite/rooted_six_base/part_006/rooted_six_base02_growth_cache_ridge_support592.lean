module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport592Part000
public import RootedSixBase02GrowthCacheRidgeSupport592Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport592_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport592_rest_012 =
    (ridgeSupport592_suffix_012, ridgeSupport592_rest_012) := by rfl
theorem ridgeSupport592_suffix_decode_011 : PackedRawNatGrowth.readList 13 3 ridgeSupport592_rest_011 =
    (ridgeSupport592_suffix_011, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 3 0
    ridgeSupport592_rest_011 ridgeSupport592_rest_012 ridgeSupport592_rest_012
    ridgeSupport592_011 ridgeSupport592_suffix_012 ridgeSupport592_011_decode ridgeSupport592_suffix_decode_012
theorem ridgeSupport592_suffix_decode_010 : PackedRawNatGrowth.readList 13 35 ridgeSupport592_rest_010 =
    (ridgeSupport592_suffix_010, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3
    ridgeSupport592_rest_010 ridgeSupport592_rest_011 ridgeSupport592_rest_012
    ridgeSupport592_010 ridgeSupport592_suffix_011 ridgeSupport592_010_decode ridgeSupport592_suffix_decode_011
theorem ridgeSupport592_suffix_decode_009 : PackedRawNatGrowth.readList 13 67 ridgeSupport592_rest_009 =
    (ridgeSupport592_suffix_009, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 35
    ridgeSupport592_rest_009 ridgeSupport592_rest_010 ridgeSupport592_rest_012
    ridgeSupport592_009 ridgeSupport592_suffix_010 ridgeSupport592_009_decode ridgeSupport592_suffix_decode_010
theorem ridgeSupport592_suffix_decode_008 : PackedRawNatGrowth.readList 13 99 ridgeSupport592_rest_008 =
    (ridgeSupport592_suffix_008, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 67
    ridgeSupport592_rest_008 ridgeSupport592_rest_009 ridgeSupport592_rest_012
    ridgeSupport592_008 ridgeSupport592_suffix_009 ridgeSupport592_008_decode ridgeSupport592_suffix_decode_009
theorem ridgeSupport592_suffix_decode_007 : PackedRawNatGrowth.readList 13 131 ridgeSupport592_rest_007 =
    (ridgeSupport592_suffix_007, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 99
    ridgeSupport592_rest_007 ridgeSupport592_rest_008 ridgeSupport592_rest_012
    ridgeSupport592_007 ridgeSupport592_suffix_008 ridgeSupport592_007_decode ridgeSupport592_suffix_decode_008
theorem ridgeSupport592_suffix_decode_006 : PackedRawNatGrowth.readList 13 163 ridgeSupport592_rest_006 =
    (ridgeSupport592_suffix_006, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 131
    ridgeSupport592_rest_006 ridgeSupport592_rest_007 ridgeSupport592_rest_012
    ridgeSupport592_006 ridgeSupport592_suffix_007 ridgeSupport592_006_decode ridgeSupport592_suffix_decode_007
theorem ridgeSupport592_suffix_decode_005 : PackedRawNatGrowth.readList 13 195 ridgeSupport592_rest_005 =
    (ridgeSupport592_suffix_005, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 163
    ridgeSupport592_rest_005 ridgeSupport592_rest_006 ridgeSupport592_rest_012
    ridgeSupport592_005 ridgeSupport592_suffix_006 ridgeSupport592_005_decode ridgeSupport592_suffix_decode_006
theorem ridgeSupport592_suffix_decode_004 : PackedRawNatGrowth.readList 13 227 ridgeSupport592_rest_004 =
    (ridgeSupport592_suffix_004, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 195
    ridgeSupport592_rest_004 ridgeSupport592_rest_005 ridgeSupport592_rest_012
    ridgeSupport592_004 ridgeSupport592_suffix_005 ridgeSupport592_004_decode ridgeSupport592_suffix_decode_005
theorem ridgeSupport592_suffix_decode_003 : PackedRawNatGrowth.readList 13 259 ridgeSupport592_rest_003 =
    (ridgeSupport592_suffix_003, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 227
    ridgeSupport592_rest_003 ridgeSupport592_rest_004 ridgeSupport592_rest_012
    ridgeSupport592_003 ridgeSupport592_suffix_004 ridgeSupport592_003_decode ridgeSupport592_suffix_decode_004
theorem ridgeSupport592_suffix_decode_002 : PackedRawNatGrowth.readList 13 291 ridgeSupport592_rest_002 =
    (ridgeSupport592_suffix_002, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 259
    ridgeSupport592_rest_002 ridgeSupport592_rest_003 ridgeSupport592_rest_012
    ridgeSupport592_002 ridgeSupport592_suffix_003 ridgeSupport592_002_decode ridgeSupport592_suffix_decode_003
theorem ridgeSupport592_suffix_decode_001 : PackedRawNatGrowth.readList 13 323 ridgeSupport592_rest_001 =
    (ridgeSupport592_suffix_001, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 291
    ridgeSupport592_rest_001 ridgeSupport592_rest_002 ridgeSupport592_rest_012
    ridgeSupport592_001 ridgeSupport592_suffix_002 ridgeSupport592_001_decode ridgeSupport592_suffix_decode_002
theorem ridgeSupport592_suffix_decode_000 : PackedRawNatGrowth.readList 13 355 ridgeSupport592_rest_000 =
    (ridgeSupport592_suffix_000, ridgeSupport592_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 323
    ridgeSupport592_rest_000 ridgeSupport592_rest_001 ridgeSupport592_rest_012
    ridgeSupport592_000 ridgeSupport592_suffix_001 ridgeSupport592_000_decode ridgeSupport592_suffix_decode_001
theorem ridgeSupport592_eq : candidateRows 592 = ridgeSupport592_suffix_000 := by
  change candidateSupports 592 = ridgeSupport592_suffix_000
  rw [ridgeSupport592_source]
  exact congrArg Prod.fst ridgeSupport592_suffix_decode_000
theorem ridgeTest_large_592 : ridgeTest 592 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport592_eq]
    simp only [ridgeSupport592_suffix_000, ridgeSupport592_suffix_001, ridgeSupport592_suffix_002, ridgeSupport592_suffix_003, ridgeSupport592_suffix_004, ridgeSupport592_suffix_005, ridgeSupport592_suffix_006, ridgeSupport592_suffix_007, ridgeSupport592_suffix_008, ridgeSupport592_suffix_009, ridgeSupport592_suffix_010, ridgeSupport592_suffix_011, ridgeSupport592_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport592_000_mask, ridgeSupport592_001_mask, ridgeSupport592_002_mask, ridgeSupport592_003_mask, ridgeSupport592_004_mask, ridgeSupport592_005_mask, ridgeSupport592_006_mask, ridgeSupport592_007_mask, ridgeSupport592_008_mask, ridgeSupport592_009_mask, ridgeSupport592_010_mask, ridgeSupport592_011_mask]
    decide +kernel
  · rw [ridgeSupport592_eq]
    simp only [ridgeSupport592_suffix_000, ridgeSupport592_suffix_001, ridgeSupport592_suffix_002, ridgeSupport592_suffix_003, ridgeSupport592_suffix_004, ridgeSupport592_suffix_005, ridgeSupport592_suffix_006, ridgeSupport592_suffix_007, ridgeSupport592_suffix_008, ridgeSupport592_suffix_009, ridgeSupport592_suffix_010, ridgeSupport592_suffix_011, ridgeSupport592_suffix_012, List.all_append, List.all_nil, ridgeSupport592_000_checked, ridgeSupport592_001_checked, ridgeSupport592_002_checked, ridgeSupport592_003_checked, ridgeSupport592_004_checked, ridgeSupport592_005_checked, ridgeSupport592_006_checked, ridgeSupport592_007_checked, ridgeSupport592_008_checked, ridgeSupport592_009_checked, ridgeSupport592_010_checked, ridgeSupport592_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
