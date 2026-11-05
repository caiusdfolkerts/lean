module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport137Part000
public import RootedSixBase02GrowthCacheRidgeSupport137Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport137_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport137_rest_010 =
    (ridgeSupport137_suffix_010, ridgeSupport137_rest_010) := by rfl
theorem ridgeSupport137_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport137_rest_009 =
    (ridgeSupport137_suffix_009, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport137_rest_009 ridgeSupport137_rest_010 ridgeSupport137_rest_010
    ridgeSupport137_009 ridgeSupport137_suffix_010 ridgeSupport137_009_decode ridgeSupport137_suffix_decode_010
theorem ridgeSupport137_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport137_rest_008 =
    (ridgeSupport137_suffix_008, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport137_rest_008 ridgeSupport137_rest_009 ridgeSupport137_rest_010
    ridgeSupport137_008 ridgeSupport137_suffix_009 ridgeSupport137_008_decode ridgeSupport137_suffix_decode_009
theorem ridgeSupport137_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport137_rest_007 =
    (ridgeSupport137_suffix_007, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport137_rest_007 ridgeSupport137_rest_008 ridgeSupport137_rest_010
    ridgeSupport137_007 ridgeSupport137_suffix_008 ridgeSupport137_007_decode ridgeSupport137_suffix_decode_008
theorem ridgeSupport137_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport137_rest_006 =
    (ridgeSupport137_suffix_006, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport137_rest_006 ridgeSupport137_rest_007 ridgeSupport137_rest_010
    ridgeSupport137_006 ridgeSupport137_suffix_007 ridgeSupport137_006_decode ridgeSupport137_suffix_decode_007
theorem ridgeSupport137_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport137_rest_005 =
    (ridgeSupport137_suffix_005, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport137_rest_005 ridgeSupport137_rest_006 ridgeSupport137_rest_010
    ridgeSupport137_005 ridgeSupport137_suffix_006 ridgeSupport137_005_decode ridgeSupport137_suffix_decode_006
theorem ridgeSupport137_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport137_rest_004 =
    (ridgeSupport137_suffix_004, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport137_rest_004 ridgeSupport137_rest_005 ridgeSupport137_rest_010
    ridgeSupport137_004 ridgeSupport137_suffix_005 ridgeSupport137_004_decode ridgeSupport137_suffix_decode_005
theorem ridgeSupport137_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport137_rest_003 =
    (ridgeSupport137_suffix_003, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport137_rest_003 ridgeSupport137_rest_004 ridgeSupport137_rest_010
    ridgeSupport137_003 ridgeSupport137_suffix_004 ridgeSupport137_003_decode ridgeSupport137_suffix_decode_004
theorem ridgeSupport137_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport137_rest_002 =
    (ridgeSupport137_suffix_002, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport137_rest_002 ridgeSupport137_rest_003 ridgeSupport137_rest_010
    ridgeSupport137_002 ridgeSupport137_suffix_003 ridgeSupport137_002_decode ridgeSupport137_suffix_decode_003
theorem ridgeSupport137_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport137_rest_001 =
    (ridgeSupport137_suffix_001, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport137_rest_001 ridgeSupport137_rest_002 ridgeSupport137_rest_010
    ridgeSupport137_001 ridgeSupport137_suffix_002 ridgeSupport137_001_decode ridgeSupport137_suffix_decode_002
theorem ridgeSupport137_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport137_rest_000 =
    (ridgeSupport137_suffix_000, ridgeSupport137_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport137_rest_000 ridgeSupport137_rest_001 ridgeSupport137_rest_010
    ridgeSupport137_000 ridgeSupport137_suffix_001 ridgeSupport137_000_decode ridgeSupport137_suffix_decode_001
theorem ridgeSupport137_eq : candidateRows 137 = ridgeSupport137_suffix_000 := by
  change candidateSupports 137 = ridgeSupport137_suffix_000
  rw [ridgeSupport137_source]
  exact congrArg Prod.fst ridgeSupport137_suffix_decode_000
theorem ridgeTest_large_137 : ridgeTest 137 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport137_eq]
    simp only [ridgeSupport137_suffix_000, ridgeSupport137_suffix_001, ridgeSupport137_suffix_002, ridgeSupport137_suffix_003, ridgeSupport137_suffix_004, ridgeSupport137_suffix_005, ridgeSupport137_suffix_006, ridgeSupport137_suffix_007, ridgeSupport137_suffix_008, ridgeSupport137_suffix_009, ridgeSupport137_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport137_000_mask, ridgeSupport137_001_mask, ridgeSupport137_002_mask, ridgeSupport137_003_mask, ridgeSupport137_004_mask, ridgeSupport137_005_mask, ridgeSupport137_006_mask, ridgeSupport137_007_mask, ridgeSupport137_008_mask, ridgeSupport137_009_mask]
    decide +kernel
  · rw [ridgeSupport137_eq]
    simp only [ridgeSupport137_suffix_000, ridgeSupport137_suffix_001, ridgeSupport137_suffix_002, ridgeSupport137_suffix_003, ridgeSupport137_suffix_004, ridgeSupport137_suffix_005, ridgeSupport137_suffix_006, ridgeSupport137_suffix_007, ridgeSupport137_suffix_008, ridgeSupport137_suffix_009, ridgeSupport137_suffix_010, List.all_append, List.all_nil, ridgeSupport137_000_checked, ridgeSupport137_001_checked, ridgeSupport137_002_checked, ridgeSupport137_003_checked, ridgeSupport137_004_checked, ridgeSupport137_005_checked, ridgeSupport137_006_checked, ridgeSupport137_007_checked, ridgeSupport137_008_checked, ridgeSupport137_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
