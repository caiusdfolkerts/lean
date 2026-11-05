module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport352Part000
public import RootedSixExtra00GrowthCacheRidgeSupport352Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport352_suffix_decode_010 : PackedRawNatGrowth.readList 14 0 ridgeSupport352_rest_010 =
    (ridgeSupport352_suffix_010, ridgeSupport352_rest_010) := by rfl
theorem ridgeSupport352_suffix_decode_009 : PackedRawNatGrowth.readList 14 17 ridgeSupport352_rest_009 =
    (ridgeSupport352_suffix_009, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 17 0
    ridgeSupport352_rest_009 ridgeSupport352_rest_010 ridgeSupport352_rest_010
    ridgeSupport352_009 ridgeSupport352_suffix_010 ridgeSupport352_009_decode ridgeSupport352_suffix_decode_010
theorem ridgeSupport352_suffix_decode_008 : PackedRawNatGrowth.readList 14 49 ridgeSupport352_rest_008 =
    (ridgeSupport352_suffix_008, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 17
    ridgeSupport352_rest_008 ridgeSupport352_rest_009 ridgeSupport352_rest_010
    ridgeSupport352_008 ridgeSupport352_suffix_009 ridgeSupport352_008_decode ridgeSupport352_suffix_decode_009
theorem ridgeSupport352_suffix_decode_007 : PackedRawNatGrowth.readList 14 81 ridgeSupport352_rest_007 =
    (ridgeSupport352_suffix_007, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 49
    ridgeSupport352_rest_007 ridgeSupport352_rest_008 ridgeSupport352_rest_010
    ridgeSupport352_007 ridgeSupport352_suffix_008 ridgeSupport352_007_decode ridgeSupport352_suffix_decode_008
theorem ridgeSupport352_suffix_decode_006 : PackedRawNatGrowth.readList 14 113 ridgeSupport352_rest_006 =
    (ridgeSupport352_suffix_006, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 81
    ridgeSupport352_rest_006 ridgeSupport352_rest_007 ridgeSupport352_rest_010
    ridgeSupport352_006 ridgeSupport352_suffix_007 ridgeSupport352_006_decode ridgeSupport352_suffix_decode_007
theorem ridgeSupport352_suffix_decode_005 : PackedRawNatGrowth.readList 14 145 ridgeSupport352_rest_005 =
    (ridgeSupport352_suffix_005, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 113
    ridgeSupport352_rest_005 ridgeSupport352_rest_006 ridgeSupport352_rest_010
    ridgeSupport352_005 ridgeSupport352_suffix_006 ridgeSupport352_005_decode ridgeSupport352_suffix_decode_006
theorem ridgeSupport352_suffix_decode_004 : PackedRawNatGrowth.readList 14 177 ridgeSupport352_rest_004 =
    (ridgeSupport352_suffix_004, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 145
    ridgeSupport352_rest_004 ridgeSupport352_rest_005 ridgeSupport352_rest_010
    ridgeSupport352_004 ridgeSupport352_suffix_005 ridgeSupport352_004_decode ridgeSupport352_suffix_decode_005
theorem ridgeSupport352_suffix_decode_003 : PackedRawNatGrowth.readList 14 209 ridgeSupport352_rest_003 =
    (ridgeSupport352_suffix_003, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 177
    ridgeSupport352_rest_003 ridgeSupport352_rest_004 ridgeSupport352_rest_010
    ridgeSupport352_003 ridgeSupport352_suffix_004 ridgeSupport352_003_decode ridgeSupport352_suffix_decode_004
theorem ridgeSupport352_suffix_decode_002 : PackedRawNatGrowth.readList 14 241 ridgeSupport352_rest_002 =
    (ridgeSupport352_suffix_002, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 209
    ridgeSupport352_rest_002 ridgeSupport352_rest_003 ridgeSupport352_rest_010
    ridgeSupport352_002 ridgeSupport352_suffix_003 ridgeSupport352_002_decode ridgeSupport352_suffix_decode_003
theorem ridgeSupport352_suffix_decode_001 : PackedRawNatGrowth.readList 14 273 ridgeSupport352_rest_001 =
    (ridgeSupport352_suffix_001, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 241
    ridgeSupport352_rest_001 ridgeSupport352_rest_002 ridgeSupport352_rest_010
    ridgeSupport352_001 ridgeSupport352_suffix_002 ridgeSupport352_001_decode ridgeSupport352_suffix_decode_002
theorem ridgeSupport352_suffix_decode_000 : PackedRawNatGrowth.readList 14 305 ridgeSupport352_rest_000 =
    (ridgeSupport352_suffix_000, ridgeSupport352_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 273
    ridgeSupport352_rest_000 ridgeSupport352_rest_001 ridgeSupport352_rest_010
    ridgeSupport352_000 ridgeSupport352_suffix_001 ridgeSupport352_000_decode ridgeSupport352_suffix_decode_001
theorem ridgeSupport352_eq : candidateRows 352 = ridgeSupport352_suffix_000 := by
  change candidateSupports 352 = ridgeSupport352_suffix_000
  rw [ridgeSupport352_source]
  exact congrArg Prod.fst ridgeSupport352_suffix_decode_000
theorem ridgeTest_large_352 : ridgeTest 352 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport352_000_mask, ridgeSupport352_001_mask, ridgeSupport352_002_mask, ridgeSupport352_003_mask, ridgeSupport352_004_mask, ridgeSupport352_005_mask, ridgeSupport352_006_mask, ridgeSupport352_007_mask, ridgeSupport352_008_mask, ridgeSupport352_009_mask]
    decide +kernel
  · rw [ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, List.all_append, List.all_nil, ridgeSupport352_000_checked, ridgeSupport352_001_checked, ridgeSupport352_002_checked, ridgeSupport352_003_checked, ridgeSupport352_004_checked, ridgeSupport352_005_checked, ridgeSupport352_006_checked, ridgeSupport352_007_checked, ridgeSupport352_008_checked, ridgeSupport352_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
