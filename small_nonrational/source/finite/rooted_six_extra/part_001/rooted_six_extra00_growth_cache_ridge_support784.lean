module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport784Part000
public import RootedSixExtra00GrowthCacheRidgeSupport784Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport784_suffix_decode_013 : PackedRawNatGrowth.readList 14 0 ridgeSupport784_rest_013 =
    (ridgeSupport784_suffix_013, ridgeSupport784_rest_013) := by rfl
theorem ridgeSupport784_suffix_decode_012 : PackedRawNatGrowth.readList 14 18 ridgeSupport784_rest_012 =
    (ridgeSupport784_suffix_012, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 18 0
    ridgeSupport784_rest_012 ridgeSupport784_rest_013 ridgeSupport784_rest_013
    ridgeSupport784_012 ridgeSupport784_suffix_013 ridgeSupport784_012_decode ridgeSupport784_suffix_decode_013
theorem ridgeSupport784_suffix_decode_011 : PackedRawNatGrowth.readList 14 50 ridgeSupport784_rest_011 =
    (ridgeSupport784_suffix_011, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 18
    ridgeSupport784_rest_011 ridgeSupport784_rest_012 ridgeSupport784_rest_013
    ridgeSupport784_011 ridgeSupport784_suffix_012 ridgeSupport784_011_decode ridgeSupport784_suffix_decode_012
theorem ridgeSupport784_suffix_decode_010 : PackedRawNatGrowth.readList 14 82 ridgeSupport784_rest_010 =
    (ridgeSupport784_suffix_010, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 50
    ridgeSupport784_rest_010 ridgeSupport784_rest_011 ridgeSupport784_rest_013
    ridgeSupport784_010 ridgeSupport784_suffix_011 ridgeSupport784_010_decode ridgeSupport784_suffix_decode_011
theorem ridgeSupport784_suffix_decode_009 : PackedRawNatGrowth.readList 14 114 ridgeSupport784_rest_009 =
    (ridgeSupport784_suffix_009, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 82
    ridgeSupport784_rest_009 ridgeSupport784_rest_010 ridgeSupport784_rest_013
    ridgeSupport784_009 ridgeSupport784_suffix_010 ridgeSupport784_009_decode ridgeSupport784_suffix_decode_010
theorem ridgeSupport784_suffix_decode_008 : PackedRawNatGrowth.readList 14 146 ridgeSupport784_rest_008 =
    (ridgeSupport784_suffix_008, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 114
    ridgeSupport784_rest_008 ridgeSupport784_rest_009 ridgeSupport784_rest_013
    ridgeSupport784_008 ridgeSupport784_suffix_009 ridgeSupport784_008_decode ridgeSupport784_suffix_decode_009
theorem ridgeSupport784_suffix_decode_007 : PackedRawNatGrowth.readList 14 178 ridgeSupport784_rest_007 =
    (ridgeSupport784_suffix_007, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 146
    ridgeSupport784_rest_007 ridgeSupport784_rest_008 ridgeSupport784_rest_013
    ridgeSupport784_007 ridgeSupport784_suffix_008 ridgeSupport784_007_decode ridgeSupport784_suffix_decode_008
theorem ridgeSupport784_suffix_decode_006 : PackedRawNatGrowth.readList 14 210 ridgeSupport784_rest_006 =
    (ridgeSupport784_suffix_006, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 178
    ridgeSupport784_rest_006 ridgeSupport784_rest_007 ridgeSupport784_rest_013
    ridgeSupport784_006 ridgeSupport784_suffix_007 ridgeSupport784_006_decode ridgeSupport784_suffix_decode_007
theorem ridgeSupport784_suffix_decode_005 : PackedRawNatGrowth.readList 14 242 ridgeSupport784_rest_005 =
    (ridgeSupport784_suffix_005, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 210
    ridgeSupport784_rest_005 ridgeSupport784_rest_006 ridgeSupport784_rest_013
    ridgeSupport784_005 ridgeSupport784_suffix_006 ridgeSupport784_005_decode ridgeSupport784_suffix_decode_006
theorem ridgeSupport784_suffix_decode_004 : PackedRawNatGrowth.readList 14 274 ridgeSupport784_rest_004 =
    (ridgeSupport784_suffix_004, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 242
    ridgeSupport784_rest_004 ridgeSupport784_rest_005 ridgeSupport784_rest_013
    ridgeSupport784_004 ridgeSupport784_suffix_005 ridgeSupport784_004_decode ridgeSupport784_suffix_decode_005
theorem ridgeSupport784_suffix_decode_003 : PackedRawNatGrowth.readList 14 306 ridgeSupport784_rest_003 =
    (ridgeSupport784_suffix_003, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 274
    ridgeSupport784_rest_003 ridgeSupport784_rest_004 ridgeSupport784_rest_013
    ridgeSupport784_003 ridgeSupport784_suffix_004 ridgeSupport784_003_decode ridgeSupport784_suffix_decode_004
theorem ridgeSupport784_suffix_decode_002 : PackedRawNatGrowth.readList 14 338 ridgeSupport784_rest_002 =
    (ridgeSupport784_suffix_002, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 306
    ridgeSupport784_rest_002 ridgeSupport784_rest_003 ridgeSupport784_rest_013
    ridgeSupport784_002 ridgeSupport784_suffix_003 ridgeSupport784_002_decode ridgeSupport784_suffix_decode_003
theorem ridgeSupport784_suffix_decode_001 : PackedRawNatGrowth.readList 14 370 ridgeSupport784_rest_001 =
    (ridgeSupport784_suffix_001, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 338
    ridgeSupport784_rest_001 ridgeSupport784_rest_002 ridgeSupport784_rest_013
    ridgeSupport784_001 ridgeSupport784_suffix_002 ridgeSupport784_001_decode ridgeSupport784_suffix_decode_002
theorem ridgeSupport784_suffix_decode_000 : PackedRawNatGrowth.readList 14 402 ridgeSupport784_rest_000 =
    (ridgeSupport784_suffix_000, ridgeSupport784_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 370
    ridgeSupport784_rest_000 ridgeSupport784_rest_001 ridgeSupport784_rest_013
    ridgeSupport784_000 ridgeSupport784_suffix_001 ridgeSupport784_000_decode ridgeSupport784_suffix_decode_001
theorem ridgeSupport784_eq : candidateRows 784 = ridgeSupport784_suffix_000 := by
  change candidateSupports 784 = ridgeSupport784_suffix_000
  rw [ridgeSupport784_source]
  exact congrArg Prod.fst ridgeSupport784_suffix_decode_000
theorem ridgeTest_large_784 : ridgeTest 784 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport784_eq]
    simp only [ridgeSupport784_suffix_000, ridgeSupport784_suffix_001, ridgeSupport784_suffix_002, ridgeSupport784_suffix_003, ridgeSupport784_suffix_004, ridgeSupport784_suffix_005, ridgeSupport784_suffix_006, ridgeSupport784_suffix_007, ridgeSupport784_suffix_008, ridgeSupport784_suffix_009, ridgeSupport784_suffix_010, ridgeSupport784_suffix_011, ridgeSupport784_suffix_012, ridgeSupport784_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport784_000_mask, ridgeSupport784_001_mask, ridgeSupport784_002_mask, ridgeSupport784_003_mask, ridgeSupport784_004_mask, ridgeSupport784_005_mask, ridgeSupport784_006_mask, ridgeSupport784_007_mask, ridgeSupport784_008_mask, ridgeSupport784_009_mask, ridgeSupport784_010_mask, ridgeSupport784_011_mask, ridgeSupport784_012_mask]
    decide +kernel
  · rw [ridgeSupport784_eq]
    simp only [ridgeSupport784_suffix_000, ridgeSupport784_suffix_001, ridgeSupport784_suffix_002, ridgeSupport784_suffix_003, ridgeSupport784_suffix_004, ridgeSupport784_suffix_005, ridgeSupport784_suffix_006, ridgeSupport784_suffix_007, ridgeSupport784_suffix_008, ridgeSupport784_suffix_009, ridgeSupport784_suffix_010, ridgeSupport784_suffix_011, ridgeSupport784_suffix_012, ridgeSupport784_suffix_013, List.all_append, List.all_nil, ridgeSupport784_000_checked, ridgeSupport784_001_checked, ridgeSupport784_002_checked, ridgeSupport784_003_checked, ridgeSupport784_004_checked, ridgeSupport784_005_checked, ridgeSupport784_006_checked, ridgeSupport784_007_checked, ridgeSupport784_008_checked, ridgeSupport784_009_checked, ridgeSupport784_010_checked, ridgeSupport784_011_checked, ridgeSupport784_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
