module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport336Part000
public import RootedSixExtra00GrowthCacheRidgeSupport336Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport336_suffix_decode_013 : PackedRawNatGrowth.readList 14 0 ridgeSupport336_rest_013 =
    (ridgeSupport336_suffix_013, ridgeSupport336_rest_013) := by rfl
theorem ridgeSupport336_suffix_decode_012 : PackedRawNatGrowth.readList 14 18 ridgeSupport336_rest_012 =
    (ridgeSupport336_suffix_012, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 18 0
    ridgeSupport336_rest_012 ridgeSupport336_rest_013 ridgeSupport336_rest_013
    ridgeSupport336_012 ridgeSupport336_suffix_013 ridgeSupport336_012_decode ridgeSupport336_suffix_decode_013
theorem ridgeSupport336_suffix_decode_011 : PackedRawNatGrowth.readList 14 50 ridgeSupport336_rest_011 =
    (ridgeSupport336_suffix_011, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 18
    ridgeSupport336_rest_011 ridgeSupport336_rest_012 ridgeSupport336_rest_013
    ridgeSupport336_011 ridgeSupport336_suffix_012 ridgeSupport336_011_decode ridgeSupport336_suffix_decode_012
theorem ridgeSupport336_suffix_decode_010 : PackedRawNatGrowth.readList 14 82 ridgeSupport336_rest_010 =
    (ridgeSupport336_suffix_010, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 50
    ridgeSupport336_rest_010 ridgeSupport336_rest_011 ridgeSupport336_rest_013
    ridgeSupport336_010 ridgeSupport336_suffix_011 ridgeSupport336_010_decode ridgeSupport336_suffix_decode_011
theorem ridgeSupport336_suffix_decode_009 : PackedRawNatGrowth.readList 14 114 ridgeSupport336_rest_009 =
    (ridgeSupport336_suffix_009, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 82
    ridgeSupport336_rest_009 ridgeSupport336_rest_010 ridgeSupport336_rest_013
    ridgeSupport336_009 ridgeSupport336_suffix_010 ridgeSupport336_009_decode ridgeSupport336_suffix_decode_010
theorem ridgeSupport336_suffix_decode_008 : PackedRawNatGrowth.readList 14 146 ridgeSupport336_rest_008 =
    (ridgeSupport336_suffix_008, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 114
    ridgeSupport336_rest_008 ridgeSupport336_rest_009 ridgeSupport336_rest_013
    ridgeSupport336_008 ridgeSupport336_suffix_009 ridgeSupport336_008_decode ridgeSupport336_suffix_decode_009
theorem ridgeSupport336_suffix_decode_007 : PackedRawNatGrowth.readList 14 178 ridgeSupport336_rest_007 =
    (ridgeSupport336_suffix_007, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 146
    ridgeSupport336_rest_007 ridgeSupport336_rest_008 ridgeSupport336_rest_013
    ridgeSupport336_007 ridgeSupport336_suffix_008 ridgeSupport336_007_decode ridgeSupport336_suffix_decode_008
theorem ridgeSupport336_suffix_decode_006 : PackedRawNatGrowth.readList 14 210 ridgeSupport336_rest_006 =
    (ridgeSupport336_suffix_006, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 178
    ridgeSupport336_rest_006 ridgeSupport336_rest_007 ridgeSupport336_rest_013
    ridgeSupport336_006 ridgeSupport336_suffix_007 ridgeSupport336_006_decode ridgeSupport336_suffix_decode_007
theorem ridgeSupport336_suffix_decode_005 : PackedRawNatGrowth.readList 14 242 ridgeSupport336_rest_005 =
    (ridgeSupport336_suffix_005, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 210
    ridgeSupport336_rest_005 ridgeSupport336_rest_006 ridgeSupport336_rest_013
    ridgeSupport336_005 ridgeSupport336_suffix_006 ridgeSupport336_005_decode ridgeSupport336_suffix_decode_006
theorem ridgeSupport336_suffix_decode_004 : PackedRawNatGrowth.readList 14 274 ridgeSupport336_rest_004 =
    (ridgeSupport336_suffix_004, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 242
    ridgeSupport336_rest_004 ridgeSupport336_rest_005 ridgeSupport336_rest_013
    ridgeSupport336_004 ridgeSupport336_suffix_005 ridgeSupport336_004_decode ridgeSupport336_suffix_decode_005
theorem ridgeSupport336_suffix_decode_003 : PackedRawNatGrowth.readList 14 306 ridgeSupport336_rest_003 =
    (ridgeSupport336_suffix_003, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 274
    ridgeSupport336_rest_003 ridgeSupport336_rest_004 ridgeSupport336_rest_013
    ridgeSupport336_003 ridgeSupport336_suffix_004 ridgeSupport336_003_decode ridgeSupport336_suffix_decode_004
theorem ridgeSupport336_suffix_decode_002 : PackedRawNatGrowth.readList 14 338 ridgeSupport336_rest_002 =
    (ridgeSupport336_suffix_002, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 306
    ridgeSupport336_rest_002 ridgeSupport336_rest_003 ridgeSupport336_rest_013
    ridgeSupport336_002 ridgeSupport336_suffix_003 ridgeSupport336_002_decode ridgeSupport336_suffix_decode_003
theorem ridgeSupport336_suffix_decode_001 : PackedRawNatGrowth.readList 14 370 ridgeSupport336_rest_001 =
    (ridgeSupport336_suffix_001, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 338
    ridgeSupport336_rest_001 ridgeSupport336_rest_002 ridgeSupport336_rest_013
    ridgeSupport336_001 ridgeSupport336_suffix_002 ridgeSupport336_001_decode ridgeSupport336_suffix_decode_002
theorem ridgeSupport336_suffix_decode_000 : PackedRawNatGrowth.readList 14 402 ridgeSupport336_rest_000 =
    (ridgeSupport336_suffix_000, ridgeSupport336_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 370
    ridgeSupport336_rest_000 ridgeSupport336_rest_001 ridgeSupport336_rest_013
    ridgeSupport336_000 ridgeSupport336_suffix_001 ridgeSupport336_000_decode ridgeSupport336_suffix_decode_001
theorem ridgeSupport336_eq : candidateRows 336 = ridgeSupport336_suffix_000 := by
  change candidateSupports 336 = ridgeSupport336_suffix_000
  rw [ridgeSupport336_source]
  exact congrArg Prod.fst ridgeSupport336_suffix_decode_000
theorem ridgeTest_large_336 : ridgeTest 336 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport336_eq]
    simp only [ridgeSupport336_suffix_000, ridgeSupport336_suffix_001, ridgeSupport336_suffix_002, ridgeSupport336_suffix_003, ridgeSupport336_suffix_004, ridgeSupport336_suffix_005, ridgeSupport336_suffix_006, ridgeSupport336_suffix_007, ridgeSupport336_suffix_008, ridgeSupport336_suffix_009, ridgeSupport336_suffix_010, ridgeSupport336_suffix_011, ridgeSupport336_suffix_012, ridgeSupport336_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport336_000_mask, ridgeSupport336_001_mask, ridgeSupport336_002_mask, ridgeSupport336_003_mask, ridgeSupport336_004_mask, ridgeSupport336_005_mask, ridgeSupport336_006_mask, ridgeSupport336_007_mask, ridgeSupport336_008_mask, ridgeSupport336_009_mask, ridgeSupport336_010_mask, ridgeSupport336_011_mask, ridgeSupport336_012_mask]
    decide +kernel
  · rw [ridgeSupport336_eq]
    simp only [ridgeSupport336_suffix_000, ridgeSupport336_suffix_001, ridgeSupport336_suffix_002, ridgeSupport336_suffix_003, ridgeSupport336_suffix_004, ridgeSupport336_suffix_005, ridgeSupport336_suffix_006, ridgeSupport336_suffix_007, ridgeSupport336_suffix_008, ridgeSupport336_suffix_009, ridgeSupport336_suffix_010, ridgeSupport336_suffix_011, ridgeSupport336_suffix_012, ridgeSupport336_suffix_013, List.all_append, List.all_nil, ridgeSupport336_000_checked, ridgeSupport336_001_checked, ridgeSupport336_002_checked, ridgeSupport336_003_checked, ridgeSupport336_004_checked, ridgeSupport336_005_checked, ridgeSupport336_006_checked, ridgeSupport336_007_checked, ridgeSupport336_008_checked, ridgeSupport336_009_checked, ridgeSupport336_010_checked, ridgeSupport336_011_checked, ridgeSupport336_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
