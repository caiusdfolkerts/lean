module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport656Part000
public import RootedSixExtra00GrowthCacheRidgeSupport656Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport656_suffix_decode_013 : PackedRawNatGrowth.readList 14 0 ridgeSupport656_rest_013 =
    (ridgeSupport656_suffix_013, ridgeSupport656_rest_013) := by rfl
theorem ridgeSupport656_suffix_decode_012 : PackedRawNatGrowth.readList 14 18 ridgeSupport656_rest_012 =
    (ridgeSupport656_suffix_012, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 18 0
    ridgeSupport656_rest_012 ridgeSupport656_rest_013 ridgeSupport656_rest_013
    ridgeSupport656_012 ridgeSupport656_suffix_013 ridgeSupport656_012_decode ridgeSupport656_suffix_decode_013
theorem ridgeSupport656_suffix_decode_011 : PackedRawNatGrowth.readList 14 50 ridgeSupport656_rest_011 =
    (ridgeSupport656_suffix_011, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 18
    ridgeSupport656_rest_011 ridgeSupport656_rest_012 ridgeSupport656_rest_013
    ridgeSupport656_011 ridgeSupport656_suffix_012 ridgeSupport656_011_decode ridgeSupport656_suffix_decode_012
theorem ridgeSupport656_suffix_decode_010 : PackedRawNatGrowth.readList 14 82 ridgeSupport656_rest_010 =
    (ridgeSupport656_suffix_010, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 50
    ridgeSupport656_rest_010 ridgeSupport656_rest_011 ridgeSupport656_rest_013
    ridgeSupport656_010 ridgeSupport656_suffix_011 ridgeSupport656_010_decode ridgeSupport656_suffix_decode_011
theorem ridgeSupport656_suffix_decode_009 : PackedRawNatGrowth.readList 14 114 ridgeSupport656_rest_009 =
    (ridgeSupport656_suffix_009, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 82
    ridgeSupport656_rest_009 ridgeSupport656_rest_010 ridgeSupport656_rest_013
    ridgeSupport656_009 ridgeSupport656_suffix_010 ridgeSupport656_009_decode ridgeSupport656_suffix_decode_010
theorem ridgeSupport656_suffix_decode_008 : PackedRawNatGrowth.readList 14 146 ridgeSupport656_rest_008 =
    (ridgeSupport656_suffix_008, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 114
    ridgeSupport656_rest_008 ridgeSupport656_rest_009 ridgeSupport656_rest_013
    ridgeSupport656_008 ridgeSupport656_suffix_009 ridgeSupport656_008_decode ridgeSupport656_suffix_decode_009
theorem ridgeSupport656_suffix_decode_007 : PackedRawNatGrowth.readList 14 178 ridgeSupport656_rest_007 =
    (ridgeSupport656_suffix_007, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 146
    ridgeSupport656_rest_007 ridgeSupport656_rest_008 ridgeSupport656_rest_013
    ridgeSupport656_007 ridgeSupport656_suffix_008 ridgeSupport656_007_decode ridgeSupport656_suffix_decode_008
theorem ridgeSupport656_suffix_decode_006 : PackedRawNatGrowth.readList 14 210 ridgeSupport656_rest_006 =
    (ridgeSupport656_suffix_006, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 178
    ridgeSupport656_rest_006 ridgeSupport656_rest_007 ridgeSupport656_rest_013
    ridgeSupport656_006 ridgeSupport656_suffix_007 ridgeSupport656_006_decode ridgeSupport656_suffix_decode_007
theorem ridgeSupport656_suffix_decode_005 : PackedRawNatGrowth.readList 14 242 ridgeSupport656_rest_005 =
    (ridgeSupport656_suffix_005, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 210
    ridgeSupport656_rest_005 ridgeSupport656_rest_006 ridgeSupport656_rest_013
    ridgeSupport656_005 ridgeSupport656_suffix_006 ridgeSupport656_005_decode ridgeSupport656_suffix_decode_006
theorem ridgeSupport656_suffix_decode_004 : PackedRawNatGrowth.readList 14 274 ridgeSupport656_rest_004 =
    (ridgeSupport656_suffix_004, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 242
    ridgeSupport656_rest_004 ridgeSupport656_rest_005 ridgeSupport656_rest_013
    ridgeSupport656_004 ridgeSupport656_suffix_005 ridgeSupport656_004_decode ridgeSupport656_suffix_decode_005
theorem ridgeSupport656_suffix_decode_003 : PackedRawNatGrowth.readList 14 306 ridgeSupport656_rest_003 =
    (ridgeSupport656_suffix_003, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 274
    ridgeSupport656_rest_003 ridgeSupport656_rest_004 ridgeSupport656_rest_013
    ridgeSupport656_003 ridgeSupport656_suffix_004 ridgeSupport656_003_decode ridgeSupport656_suffix_decode_004
theorem ridgeSupport656_suffix_decode_002 : PackedRawNatGrowth.readList 14 338 ridgeSupport656_rest_002 =
    (ridgeSupport656_suffix_002, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 306
    ridgeSupport656_rest_002 ridgeSupport656_rest_003 ridgeSupport656_rest_013
    ridgeSupport656_002 ridgeSupport656_suffix_003 ridgeSupport656_002_decode ridgeSupport656_suffix_decode_003
theorem ridgeSupport656_suffix_decode_001 : PackedRawNatGrowth.readList 14 370 ridgeSupport656_rest_001 =
    (ridgeSupport656_suffix_001, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 338
    ridgeSupport656_rest_001 ridgeSupport656_rest_002 ridgeSupport656_rest_013
    ridgeSupport656_001 ridgeSupport656_suffix_002 ridgeSupport656_001_decode ridgeSupport656_suffix_decode_002
theorem ridgeSupport656_suffix_decode_000 : PackedRawNatGrowth.readList 14 402 ridgeSupport656_rest_000 =
    (ridgeSupport656_suffix_000, ridgeSupport656_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 370
    ridgeSupport656_rest_000 ridgeSupport656_rest_001 ridgeSupport656_rest_013
    ridgeSupport656_000 ridgeSupport656_suffix_001 ridgeSupport656_000_decode ridgeSupport656_suffix_decode_001
theorem ridgeSupport656_eq : candidateRows 656 = ridgeSupport656_suffix_000 := by
  change candidateSupports 656 = ridgeSupport656_suffix_000
  rw [ridgeSupport656_source]
  exact congrArg Prod.fst ridgeSupport656_suffix_decode_000
theorem ridgeTest_large_656 : ridgeTest 656 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, ridgeSupport656_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport656_000_mask, ridgeSupport656_001_mask, ridgeSupport656_002_mask, ridgeSupport656_003_mask, ridgeSupport656_004_mask, ridgeSupport656_005_mask, ridgeSupport656_006_mask, ridgeSupport656_007_mask, ridgeSupport656_008_mask, ridgeSupport656_009_mask, ridgeSupport656_010_mask, ridgeSupport656_011_mask, ridgeSupport656_012_mask]
    decide +kernel
  · rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, ridgeSupport656_suffix_013, List.all_append, List.all_nil, ridgeSupport656_000_checked, ridgeSupport656_001_checked, ridgeSupport656_002_checked, ridgeSupport656_003_checked, ridgeSupport656_004_checked, ridgeSupport656_005_checked, ridgeSupport656_006_checked, ridgeSupport656_007_checked, ridgeSupport656_008_checked, ridgeSupport656_009_checked, ridgeSupport656_010_checked, ridgeSupport656_011_checked, ridgeSupport656_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
