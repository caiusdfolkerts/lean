module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport400Part000
public import RootedSixBase02GrowthCacheRidgeSupport400Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport400_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport400_rest_012 =
    (ridgeSupport400_suffix_012, ridgeSupport400_rest_012) := by rfl
theorem ridgeSupport400_suffix_decode_011 : PackedRawNatGrowth.readList 13 3 ridgeSupport400_rest_011 =
    (ridgeSupport400_suffix_011, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 3 0
    ridgeSupport400_rest_011 ridgeSupport400_rest_012 ridgeSupport400_rest_012
    ridgeSupport400_011 ridgeSupport400_suffix_012 ridgeSupport400_011_decode ridgeSupport400_suffix_decode_012
theorem ridgeSupport400_suffix_decode_010 : PackedRawNatGrowth.readList 13 35 ridgeSupport400_rest_010 =
    (ridgeSupport400_suffix_010, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3
    ridgeSupport400_rest_010 ridgeSupport400_rest_011 ridgeSupport400_rest_012
    ridgeSupport400_010 ridgeSupport400_suffix_011 ridgeSupport400_010_decode ridgeSupport400_suffix_decode_011
theorem ridgeSupport400_suffix_decode_009 : PackedRawNatGrowth.readList 13 67 ridgeSupport400_rest_009 =
    (ridgeSupport400_suffix_009, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 35
    ridgeSupport400_rest_009 ridgeSupport400_rest_010 ridgeSupport400_rest_012
    ridgeSupport400_009 ridgeSupport400_suffix_010 ridgeSupport400_009_decode ridgeSupport400_suffix_decode_010
theorem ridgeSupport400_suffix_decode_008 : PackedRawNatGrowth.readList 13 99 ridgeSupport400_rest_008 =
    (ridgeSupport400_suffix_008, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 67
    ridgeSupport400_rest_008 ridgeSupport400_rest_009 ridgeSupport400_rest_012
    ridgeSupport400_008 ridgeSupport400_suffix_009 ridgeSupport400_008_decode ridgeSupport400_suffix_decode_009
theorem ridgeSupport400_suffix_decode_007 : PackedRawNatGrowth.readList 13 131 ridgeSupport400_rest_007 =
    (ridgeSupport400_suffix_007, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 99
    ridgeSupport400_rest_007 ridgeSupport400_rest_008 ridgeSupport400_rest_012
    ridgeSupport400_007 ridgeSupport400_suffix_008 ridgeSupport400_007_decode ridgeSupport400_suffix_decode_008
theorem ridgeSupport400_suffix_decode_006 : PackedRawNatGrowth.readList 13 163 ridgeSupport400_rest_006 =
    (ridgeSupport400_suffix_006, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 131
    ridgeSupport400_rest_006 ridgeSupport400_rest_007 ridgeSupport400_rest_012
    ridgeSupport400_006 ridgeSupport400_suffix_007 ridgeSupport400_006_decode ridgeSupport400_suffix_decode_007
theorem ridgeSupport400_suffix_decode_005 : PackedRawNatGrowth.readList 13 195 ridgeSupport400_rest_005 =
    (ridgeSupport400_suffix_005, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 163
    ridgeSupport400_rest_005 ridgeSupport400_rest_006 ridgeSupport400_rest_012
    ridgeSupport400_005 ridgeSupport400_suffix_006 ridgeSupport400_005_decode ridgeSupport400_suffix_decode_006
theorem ridgeSupport400_suffix_decode_004 : PackedRawNatGrowth.readList 13 227 ridgeSupport400_rest_004 =
    (ridgeSupport400_suffix_004, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 195
    ridgeSupport400_rest_004 ridgeSupport400_rest_005 ridgeSupport400_rest_012
    ridgeSupport400_004 ridgeSupport400_suffix_005 ridgeSupport400_004_decode ridgeSupport400_suffix_decode_005
theorem ridgeSupport400_suffix_decode_003 : PackedRawNatGrowth.readList 13 259 ridgeSupport400_rest_003 =
    (ridgeSupport400_suffix_003, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 227
    ridgeSupport400_rest_003 ridgeSupport400_rest_004 ridgeSupport400_rest_012
    ridgeSupport400_003 ridgeSupport400_suffix_004 ridgeSupport400_003_decode ridgeSupport400_suffix_decode_004
theorem ridgeSupport400_suffix_decode_002 : PackedRawNatGrowth.readList 13 291 ridgeSupport400_rest_002 =
    (ridgeSupport400_suffix_002, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 259
    ridgeSupport400_rest_002 ridgeSupport400_rest_003 ridgeSupport400_rest_012
    ridgeSupport400_002 ridgeSupport400_suffix_003 ridgeSupport400_002_decode ridgeSupport400_suffix_decode_003
theorem ridgeSupport400_suffix_decode_001 : PackedRawNatGrowth.readList 13 323 ridgeSupport400_rest_001 =
    (ridgeSupport400_suffix_001, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 291
    ridgeSupport400_rest_001 ridgeSupport400_rest_002 ridgeSupport400_rest_012
    ridgeSupport400_001 ridgeSupport400_suffix_002 ridgeSupport400_001_decode ridgeSupport400_suffix_decode_002
theorem ridgeSupport400_suffix_decode_000 : PackedRawNatGrowth.readList 13 355 ridgeSupport400_rest_000 =
    (ridgeSupport400_suffix_000, ridgeSupport400_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 323
    ridgeSupport400_rest_000 ridgeSupport400_rest_001 ridgeSupport400_rest_012
    ridgeSupport400_000 ridgeSupport400_suffix_001 ridgeSupport400_000_decode ridgeSupport400_suffix_decode_001
theorem ridgeSupport400_eq : candidateRows 400 = ridgeSupport400_suffix_000 := by
  change candidateSupports 400 = ridgeSupport400_suffix_000
  rw [ridgeSupport400_source]
  exact congrArg Prod.fst ridgeSupport400_suffix_decode_000
theorem ridgeTest_large_400 : ridgeTest 400 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport400_eq]
    simp only [ridgeSupport400_suffix_000, ridgeSupport400_suffix_001, ridgeSupport400_suffix_002, ridgeSupport400_suffix_003, ridgeSupport400_suffix_004, ridgeSupport400_suffix_005, ridgeSupport400_suffix_006, ridgeSupport400_suffix_007, ridgeSupport400_suffix_008, ridgeSupport400_suffix_009, ridgeSupport400_suffix_010, ridgeSupport400_suffix_011, ridgeSupport400_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport400_000_mask, ridgeSupport400_001_mask, ridgeSupport400_002_mask, ridgeSupport400_003_mask, ridgeSupport400_004_mask, ridgeSupport400_005_mask, ridgeSupport400_006_mask, ridgeSupport400_007_mask, ridgeSupport400_008_mask, ridgeSupport400_009_mask, ridgeSupport400_010_mask, ridgeSupport400_011_mask]
    decide +kernel
  · rw [ridgeSupport400_eq]
    simp only [ridgeSupport400_suffix_000, ridgeSupport400_suffix_001, ridgeSupport400_suffix_002, ridgeSupport400_suffix_003, ridgeSupport400_suffix_004, ridgeSupport400_suffix_005, ridgeSupport400_suffix_006, ridgeSupport400_suffix_007, ridgeSupport400_suffix_008, ridgeSupport400_suffix_009, ridgeSupport400_suffix_010, ridgeSupport400_suffix_011, ridgeSupport400_suffix_012, List.all_append, List.all_nil, ridgeSupport400_000_checked, ridgeSupport400_001_checked, ridgeSupport400_002_checked, ridgeSupport400_003_checked, ridgeSupport400_004_checked, ridgeSupport400_005_checked, ridgeSupport400_006_checked, ridgeSupport400_007_checked, ridgeSupport400_008_checked, ridgeSupport400_009_checked, ridgeSupport400_010_checked, ridgeSupport400_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
