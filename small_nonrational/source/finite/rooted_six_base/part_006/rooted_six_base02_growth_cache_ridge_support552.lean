module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport552Part000
public import RootedSixBase02GrowthCacheRidgeSupport552Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport552_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport552_rest_012 =
    (ridgeSupport552_suffix_012, ridgeSupport552_rest_012) := by rfl
theorem ridgeSupport552_suffix_decode_011 : PackedRawNatGrowth.readList 13 25 ridgeSupport552_rest_011 =
    (ridgeSupport552_suffix_011, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 25 0
    ridgeSupport552_rest_011 ridgeSupport552_rest_012 ridgeSupport552_rest_012
    ridgeSupport552_011 ridgeSupport552_suffix_012 ridgeSupport552_011_decode ridgeSupport552_suffix_decode_012
theorem ridgeSupport552_suffix_decode_010 : PackedRawNatGrowth.readList 13 57 ridgeSupport552_rest_010 =
    (ridgeSupport552_suffix_010, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 25
    ridgeSupport552_rest_010 ridgeSupport552_rest_011 ridgeSupport552_rest_012
    ridgeSupport552_010 ridgeSupport552_suffix_011 ridgeSupport552_010_decode ridgeSupport552_suffix_decode_011
theorem ridgeSupport552_suffix_decode_009 : PackedRawNatGrowth.readList 13 89 ridgeSupport552_rest_009 =
    (ridgeSupport552_suffix_009, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 57
    ridgeSupport552_rest_009 ridgeSupport552_rest_010 ridgeSupport552_rest_012
    ridgeSupport552_009 ridgeSupport552_suffix_010 ridgeSupport552_009_decode ridgeSupport552_suffix_decode_010
theorem ridgeSupport552_suffix_decode_008 : PackedRawNatGrowth.readList 13 121 ridgeSupport552_rest_008 =
    (ridgeSupport552_suffix_008, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 89
    ridgeSupport552_rest_008 ridgeSupport552_rest_009 ridgeSupport552_rest_012
    ridgeSupport552_008 ridgeSupport552_suffix_009 ridgeSupport552_008_decode ridgeSupport552_suffix_decode_009
theorem ridgeSupport552_suffix_decode_007 : PackedRawNatGrowth.readList 13 153 ridgeSupport552_rest_007 =
    (ridgeSupport552_suffix_007, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 121
    ridgeSupport552_rest_007 ridgeSupport552_rest_008 ridgeSupport552_rest_012
    ridgeSupport552_007 ridgeSupport552_suffix_008 ridgeSupport552_007_decode ridgeSupport552_suffix_decode_008
theorem ridgeSupport552_suffix_decode_006 : PackedRawNatGrowth.readList 13 185 ridgeSupport552_rest_006 =
    (ridgeSupport552_suffix_006, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 153
    ridgeSupport552_rest_006 ridgeSupport552_rest_007 ridgeSupport552_rest_012
    ridgeSupport552_006 ridgeSupport552_suffix_007 ridgeSupport552_006_decode ridgeSupport552_suffix_decode_007
theorem ridgeSupport552_suffix_decode_005 : PackedRawNatGrowth.readList 13 217 ridgeSupport552_rest_005 =
    (ridgeSupport552_suffix_005, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 185
    ridgeSupport552_rest_005 ridgeSupport552_rest_006 ridgeSupport552_rest_012
    ridgeSupport552_005 ridgeSupport552_suffix_006 ridgeSupport552_005_decode ridgeSupport552_suffix_decode_006
theorem ridgeSupport552_suffix_decode_004 : PackedRawNatGrowth.readList 13 249 ridgeSupport552_rest_004 =
    (ridgeSupport552_suffix_004, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 217
    ridgeSupport552_rest_004 ridgeSupport552_rest_005 ridgeSupport552_rest_012
    ridgeSupport552_004 ridgeSupport552_suffix_005 ridgeSupport552_004_decode ridgeSupport552_suffix_decode_005
theorem ridgeSupport552_suffix_decode_003 : PackedRawNatGrowth.readList 13 281 ridgeSupport552_rest_003 =
    (ridgeSupport552_suffix_003, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 249
    ridgeSupport552_rest_003 ridgeSupport552_rest_004 ridgeSupport552_rest_012
    ridgeSupport552_003 ridgeSupport552_suffix_004 ridgeSupport552_003_decode ridgeSupport552_suffix_decode_004
theorem ridgeSupport552_suffix_decode_002 : PackedRawNatGrowth.readList 13 313 ridgeSupport552_rest_002 =
    (ridgeSupport552_suffix_002, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 281
    ridgeSupport552_rest_002 ridgeSupport552_rest_003 ridgeSupport552_rest_012
    ridgeSupport552_002 ridgeSupport552_suffix_003 ridgeSupport552_002_decode ridgeSupport552_suffix_decode_003
theorem ridgeSupport552_suffix_decode_001 : PackedRawNatGrowth.readList 13 345 ridgeSupport552_rest_001 =
    (ridgeSupport552_suffix_001, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 313
    ridgeSupport552_rest_001 ridgeSupport552_rest_002 ridgeSupport552_rest_012
    ridgeSupport552_001 ridgeSupport552_suffix_002 ridgeSupport552_001_decode ridgeSupport552_suffix_decode_002
theorem ridgeSupport552_suffix_decode_000 : PackedRawNatGrowth.readList 13 377 ridgeSupport552_rest_000 =
    (ridgeSupport552_suffix_000, ridgeSupport552_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 345
    ridgeSupport552_rest_000 ridgeSupport552_rest_001 ridgeSupport552_rest_012
    ridgeSupport552_000 ridgeSupport552_suffix_001 ridgeSupport552_000_decode ridgeSupport552_suffix_decode_001
theorem ridgeSupport552_eq : candidateRows 552 = ridgeSupport552_suffix_000 := by
  change candidateSupports 552 = ridgeSupport552_suffix_000
  rw [ridgeSupport552_source]
  exact congrArg Prod.fst ridgeSupport552_suffix_decode_000
theorem ridgeTest_large_552 : ridgeTest 552 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport552_eq]
    simp only [ridgeSupport552_suffix_000, ridgeSupport552_suffix_001, ridgeSupport552_suffix_002, ridgeSupport552_suffix_003, ridgeSupport552_suffix_004, ridgeSupport552_suffix_005, ridgeSupport552_suffix_006, ridgeSupport552_suffix_007, ridgeSupport552_suffix_008, ridgeSupport552_suffix_009, ridgeSupport552_suffix_010, ridgeSupport552_suffix_011, ridgeSupport552_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport552_000_mask, ridgeSupport552_001_mask, ridgeSupport552_002_mask, ridgeSupport552_003_mask, ridgeSupport552_004_mask, ridgeSupport552_005_mask, ridgeSupport552_006_mask, ridgeSupport552_007_mask, ridgeSupport552_008_mask, ridgeSupport552_009_mask, ridgeSupport552_010_mask, ridgeSupport552_011_mask]
    decide +kernel
  · rw [ridgeSupport552_eq]
    simp only [ridgeSupport552_suffix_000, ridgeSupport552_suffix_001, ridgeSupport552_suffix_002, ridgeSupport552_suffix_003, ridgeSupport552_suffix_004, ridgeSupport552_suffix_005, ridgeSupport552_suffix_006, ridgeSupport552_suffix_007, ridgeSupport552_suffix_008, ridgeSupport552_suffix_009, ridgeSupport552_suffix_010, ridgeSupport552_suffix_011, ridgeSupport552_suffix_012, List.all_append, List.all_nil, ridgeSupport552_000_checked, ridgeSupport552_001_checked, ridgeSupport552_002_checked, ridgeSupport552_003_checked, ridgeSupport552_004_checked, ridgeSupport552_005_checked, ridgeSupport552_006_checked, ridgeSupport552_007_checked, ridgeSupport552_008_checked, ridgeSupport552_009_checked, ridgeSupport552_010_checked, ridgeSupport552_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
