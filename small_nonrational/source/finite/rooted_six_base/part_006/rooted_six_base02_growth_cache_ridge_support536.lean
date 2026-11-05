module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport536Part000
public import RootedSixBase02GrowthCacheRidgeSupport536Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport536_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport536_rest_010 =
    (ridgeSupport536_suffix_010, ridgeSupport536_rest_010) := by rfl
theorem ridgeSupport536_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport536_rest_009 =
    (ridgeSupport536_suffix_009, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport536_rest_009 ridgeSupport536_rest_010 ridgeSupport536_rest_010
    ridgeSupport536_009 ridgeSupport536_suffix_010 ridgeSupport536_009_decode ridgeSupport536_suffix_decode_010
theorem ridgeSupport536_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport536_rest_008 =
    (ridgeSupport536_suffix_008, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport536_rest_008 ridgeSupport536_rest_009 ridgeSupport536_rest_010
    ridgeSupport536_008 ridgeSupport536_suffix_009 ridgeSupport536_008_decode ridgeSupport536_suffix_decode_009
theorem ridgeSupport536_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport536_rest_007 =
    (ridgeSupport536_suffix_007, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport536_rest_007 ridgeSupport536_rest_008 ridgeSupport536_rest_010
    ridgeSupport536_007 ridgeSupport536_suffix_008 ridgeSupport536_007_decode ridgeSupport536_suffix_decode_008
theorem ridgeSupport536_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport536_rest_006 =
    (ridgeSupport536_suffix_006, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport536_rest_006 ridgeSupport536_rest_007 ridgeSupport536_rest_010
    ridgeSupport536_006 ridgeSupport536_suffix_007 ridgeSupport536_006_decode ridgeSupport536_suffix_decode_007
theorem ridgeSupport536_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport536_rest_005 =
    (ridgeSupport536_suffix_005, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport536_rest_005 ridgeSupport536_rest_006 ridgeSupport536_rest_010
    ridgeSupport536_005 ridgeSupport536_suffix_006 ridgeSupport536_005_decode ridgeSupport536_suffix_decode_006
theorem ridgeSupport536_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport536_rest_004 =
    (ridgeSupport536_suffix_004, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport536_rest_004 ridgeSupport536_rest_005 ridgeSupport536_rest_010
    ridgeSupport536_004 ridgeSupport536_suffix_005 ridgeSupport536_004_decode ridgeSupport536_suffix_decode_005
theorem ridgeSupport536_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport536_rest_003 =
    (ridgeSupport536_suffix_003, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport536_rest_003 ridgeSupport536_rest_004 ridgeSupport536_rest_010
    ridgeSupport536_003 ridgeSupport536_suffix_004 ridgeSupport536_003_decode ridgeSupport536_suffix_decode_004
theorem ridgeSupport536_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport536_rest_002 =
    (ridgeSupport536_suffix_002, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport536_rest_002 ridgeSupport536_rest_003 ridgeSupport536_rest_010
    ridgeSupport536_002 ridgeSupport536_suffix_003 ridgeSupport536_002_decode ridgeSupport536_suffix_decode_003
theorem ridgeSupport536_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport536_rest_001 =
    (ridgeSupport536_suffix_001, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport536_rest_001 ridgeSupport536_rest_002 ridgeSupport536_rest_010
    ridgeSupport536_001 ridgeSupport536_suffix_002 ridgeSupport536_001_decode ridgeSupport536_suffix_decode_002
theorem ridgeSupport536_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport536_rest_000 =
    (ridgeSupport536_suffix_000, ridgeSupport536_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport536_rest_000 ridgeSupport536_rest_001 ridgeSupport536_rest_010
    ridgeSupport536_000 ridgeSupport536_suffix_001 ridgeSupport536_000_decode ridgeSupport536_suffix_decode_001
theorem ridgeSupport536_eq : candidateRows 536 = ridgeSupport536_suffix_000 := by
  change candidateSupports 536 = ridgeSupport536_suffix_000
  rw [ridgeSupport536_source]
  exact congrArg Prod.fst ridgeSupport536_suffix_decode_000
theorem ridgeTest_large_536 : ridgeTest 536 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport536_eq]
    simp only [ridgeSupport536_suffix_000, ridgeSupport536_suffix_001, ridgeSupport536_suffix_002, ridgeSupport536_suffix_003, ridgeSupport536_suffix_004, ridgeSupport536_suffix_005, ridgeSupport536_suffix_006, ridgeSupport536_suffix_007, ridgeSupport536_suffix_008, ridgeSupport536_suffix_009, ridgeSupport536_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport536_000_mask, ridgeSupport536_001_mask, ridgeSupport536_002_mask, ridgeSupport536_003_mask, ridgeSupport536_004_mask, ridgeSupport536_005_mask, ridgeSupport536_006_mask, ridgeSupport536_007_mask, ridgeSupport536_008_mask, ridgeSupport536_009_mask]
    decide +kernel
  · rw [ridgeSupport536_eq]
    simp only [ridgeSupport536_suffix_000, ridgeSupport536_suffix_001, ridgeSupport536_suffix_002, ridgeSupport536_suffix_003, ridgeSupport536_suffix_004, ridgeSupport536_suffix_005, ridgeSupport536_suffix_006, ridgeSupport536_suffix_007, ridgeSupport536_suffix_008, ridgeSupport536_suffix_009, ridgeSupport536_suffix_010, List.all_append, List.all_nil, ridgeSupport536_000_checked, ridgeSupport536_001_checked, ridgeSupport536_002_checked, ridgeSupport536_003_checked, ridgeSupport536_004_checked, ridgeSupport536_005_checked, ridgeSupport536_006_checked, ridgeSupport536_007_checked, ridgeSupport536_008_checked, ridgeSupport536_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
