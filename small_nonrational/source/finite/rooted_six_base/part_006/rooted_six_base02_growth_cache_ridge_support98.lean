module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport98Part000
public import RootedSixBase02GrowthCacheRidgeSupport98Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport98_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport98_rest_010 =
    (ridgeSupport98_suffix_010, ridgeSupport98_rest_010) := by rfl
theorem ridgeSupport98_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport98_rest_009 =
    (ridgeSupport98_suffix_009, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport98_rest_009 ridgeSupport98_rest_010 ridgeSupport98_rest_010
    ridgeSupport98_009 ridgeSupport98_suffix_010 ridgeSupport98_009_decode ridgeSupport98_suffix_decode_010
theorem ridgeSupport98_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport98_rest_008 =
    (ridgeSupport98_suffix_008, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport98_rest_008 ridgeSupport98_rest_009 ridgeSupport98_rest_010
    ridgeSupport98_008 ridgeSupport98_suffix_009 ridgeSupport98_008_decode ridgeSupport98_suffix_decode_009
theorem ridgeSupport98_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport98_rest_007 =
    (ridgeSupport98_suffix_007, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport98_rest_007 ridgeSupport98_rest_008 ridgeSupport98_rest_010
    ridgeSupport98_007 ridgeSupport98_suffix_008 ridgeSupport98_007_decode ridgeSupport98_suffix_decode_008
theorem ridgeSupport98_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport98_rest_006 =
    (ridgeSupport98_suffix_006, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport98_rest_006 ridgeSupport98_rest_007 ridgeSupport98_rest_010
    ridgeSupport98_006 ridgeSupport98_suffix_007 ridgeSupport98_006_decode ridgeSupport98_suffix_decode_007
theorem ridgeSupport98_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport98_rest_005 =
    (ridgeSupport98_suffix_005, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport98_rest_005 ridgeSupport98_rest_006 ridgeSupport98_rest_010
    ridgeSupport98_005 ridgeSupport98_suffix_006 ridgeSupport98_005_decode ridgeSupport98_suffix_decode_006
theorem ridgeSupport98_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport98_rest_004 =
    (ridgeSupport98_suffix_004, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport98_rest_004 ridgeSupport98_rest_005 ridgeSupport98_rest_010
    ridgeSupport98_004 ridgeSupport98_suffix_005 ridgeSupport98_004_decode ridgeSupport98_suffix_decode_005
theorem ridgeSupport98_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport98_rest_003 =
    (ridgeSupport98_suffix_003, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport98_rest_003 ridgeSupport98_rest_004 ridgeSupport98_rest_010
    ridgeSupport98_003 ridgeSupport98_suffix_004 ridgeSupport98_003_decode ridgeSupport98_suffix_decode_004
theorem ridgeSupport98_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport98_rest_002 =
    (ridgeSupport98_suffix_002, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport98_rest_002 ridgeSupport98_rest_003 ridgeSupport98_rest_010
    ridgeSupport98_002 ridgeSupport98_suffix_003 ridgeSupport98_002_decode ridgeSupport98_suffix_decode_003
theorem ridgeSupport98_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport98_rest_001 =
    (ridgeSupport98_suffix_001, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport98_rest_001 ridgeSupport98_rest_002 ridgeSupport98_rest_010
    ridgeSupport98_001 ridgeSupport98_suffix_002 ridgeSupport98_001_decode ridgeSupport98_suffix_decode_002
theorem ridgeSupport98_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport98_rest_000 =
    (ridgeSupport98_suffix_000, ridgeSupport98_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport98_rest_000 ridgeSupport98_rest_001 ridgeSupport98_rest_010
    ridgeSupport98_000 ridgeSupport98_suffix_001 ridgeSupport98_000_decode ridgeSupport98_suffix_decode_001
theorem ridgeSupport98_eq : candidateRows 98 = ridgeSupport98_suffix_000 := by
  change candidateSupports 98 = ridgeSupport98_suffix_000
  rw [ridgeSupport98_source]
  exact congrArg Prod.fst ridgeSupport98_suffix_decode_000
theorem ridgeTest_large_98 : ridgeTest 98 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport98_eq]
    simp only [ridgeSupport98_suffix_000, ridgeSupport98_suffix_001, ridgeSupport98_suffix_002, ridgeSupport98_suffix_003, ridgeSupport98_suffix_004, ridgeSupport98_suffix_005, ridgeSupport98_suffix_006, ridgeSupport98_suffix_007, ridgeSupport98_suffix_008, ridgeSupport98_suffix_009, ridgeSupport98_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport98_000_mask, ridgeSupport98_001_mask, ridgeSupport98_002_mask, ridgeSupport98_003_mask, ridgeSupport98_004_mask, ridgeSupport98_005_mask, ridgeSupport98_006_mask, ridgeSupport98_007_mask, ridgeSupport98_008_mask, ridgeSupport98_009_mask]
    decide +kernel
  · rw [ridgeSupport98_eq]
    simp only [ridgeSupport98_suffix_000, ridgeSupport98_suffix_001, ridgeSupport98_suffix_002, ridgeSupport98_suffix_003, ridgeSupport98_suffix_004, ridgeSupport98_suffix_005, ridgeSupport98_suffix_006, ridgeSupport98_suffix_007, ridgeSupport98_suffix_008, ridgeSupport98_suffix_009, ridgeSupport98_suffix_010, List.all_append, List.all_nil, ridgeSupport98_000_checked, ridgeSupport98_001_checked, ridgeSupport98_002_checked, ridgeSupport98_003_checked, ridgeSupport98_004_checked, ridgeSupport98_005_checked, ridgeSupport98_006_checked, ridgeSupport98_007_checked, ridgeSupport98_008_checked, ridgeSupport98_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
