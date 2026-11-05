module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport386Part000
public import RootedSixExtra00GrowthCacheRidgeSupport386Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport386_suffix_decode_013 : PackedRawNatGrowth.readList 14 0 ridgeSupport386_rest_013 =
    (ridgeSupport386_suffix_013, ridgeSupport386_rest_013) := by rfl
theorem ridgeSupport386_suffix_decode_012 : PackedRawNatGrowth.readList 14 18 ridgeSupport386_rest_012 =
    (ridgeSupport386_suffix_012, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 18 0
    ridgeSupport386_rest_012 ridgeSupport386_rest_013 ridgeSupport386_rest_013
    ridgeSupport386_012 ridgeSupport386_suffix_013 ridgeSupport386_012_decode ridgeSupport386_suffix_decode_013
theorem ridgeSupport386_suffix_decode_011 : PackedRawNatGrowth.readList 14 50 ridgeSupport386_rest_011 =
    (ridgeSupport386_suffix_011, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 18
    ridgeSupport386_rest_011 ridgeSupport386_rest_012 ridgeSupport386_rest_013
    ridgeSupport386_011 ridgeSupport386_suffix_012 ridgeSupport386_011_decode ridgeSupport386_suffix_decode_012
theorem ridgeSupport386_suffix_decode_010 : PackedRawNatGrowth.readList 14 82 ridgeSupport386_rest_010 =
    (ridgeSupport386_suffix_010, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 50
    ridgeSupport386_rest_010 ridgeSupport386_rest_011 ridgeSupport386_rest_013
    ridgeSupport386_010 ridgeSupport386_suffix_011 ridgeSupport386_010_decode ridgeSupport386_suffix_decode_011
theorem ridgeSupport386_suffix_decode_009 : PackedRawNatGrowth.readList 14 114 ridgeSupport386_rest_009 =
    (ridgeSupport386_suffix_009, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 82
    ridgeSupport386_rest_009 ridgeSupport386_rest_010 ridgeSupport386_rest_013
    ridgeSupport386_009 ridgeSupport386_suffix_010 ridgeSupport386_009_decode ridgeSupport386_suffix_decode_010
theorem ridgeSupport386_suffix_decode_008 : PackedRawNatGrowth.readList 14 146 ridgeSupport386_rest_008 =
    (ridgeSupport386_suffix_008, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 114
    ridgeSupport386_rest_008 ridgeSupport386_rest_009 ridgeSupport386_rest_013
    ridgeSupport386_008 ridgeSupport386_suffix_009 ridgeSupport386_008_decode ridgeSupport386_suffix_decode_009
theorem ridgeSupport386_suffix_decode_007 : PackedRawNatGrowth.readList 14 178 ridgeSupport386_rest_007 =
    (ridgeSupport386_suffix_007, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 146
    ridgeSupport386_rest_007 ridgeSupport386_rest_008 ridgeSupport386_rest_013
    ridgeSupport386_007 ridgeSupport386_suffix_008 ridgeSupport386_007_decode ridgeSupport386_suffix_decode_008
theorem ridgeSupport386_suffix_decode_006 : PackedRawNatGrowth.readList 14 210 ridgeSupport386_rest_006 =
    (ridgeSupport386_suffix_006, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 178
    ridgeSupport386_rest_006 ridgeSupport386_rest_007 ridgeSupport386_rest_013
    ridgeSupport386_006 ridgeSupport386_suffix_007 ridgeSupport386_006_decode ridgeSupport386_suffix_decode_007
theorem ridgeSupport386_suffix_decode_005 : PackedRawNatGrowth.readList 14 242 ridgeSupport386_rest_005 =
    (ridgeSupport386_suffix_005, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 210
    ridgeSupport386_rest_005 ridgeSupport386_rest_006 ridgeSupport386_rest_013
    ridgeSupport386_005 ridgeSupport386_suffix_006 ridgeSupport386_005_decode ridgeSupport386_suffix_decode_006
theorem ridgeSupport386_suffix_decode_004 : PackedRawNatGrowth.readList 14 274 ridgeSupport386_rest_004 =
    (ridgeSupport386_suffix_004, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 242
    ridgeSupport386_rest_004 ridgeSupport386_rest_005 ridgeSupport386_rest_013
    ridgeSupport386_004 ridgeSupport386_suffix_005 ridgeSupport386_004_decode ridgeSupport386_suffix_decode_005
theorem ridgeSupport386_suffix_decode_003 : PackedRawNatGrowth.readList 14 306 ridgeSupport386_rest_003 =
    (ridgeSupport386_suffix_003, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 274
    ridgeSupport386_rest_003 ridgeSupport386_rest_004 ridgeSupport386_rest_013
    ridgeSupport386_003 ridgeSupport386_suffix_004 ridgeSupport386_003_decode ridgeSupport386_suffix_decode_004
theorem ridgeSupport386_suffix_decode_002 : PackedRawNatGrowth.readList 14 338 ridgeSupport386_rest_002 =
    (ridgeSupport386_suffix_002, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 306
    ridgeSupport386_rest_002 ridgeSupport386_rest_003 ridgeSupport386_rest_013
    ridgeSupport386_002 ridgeSupport386_suffix_003 ridgeSupport386_002_decode ridgeSupport386_suffix_decode_003
theorem ridgeSupport386_suffix_decode_001 : PackedRawNatGrowth.readList 14 370 ridgeSupport386_rest_001 =
    (ridgeSupport386_suffix_001, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 338
    ridgeSupport386_rest_001 ridgeSupport386_rest_002 ridgeSupport386_rest_013
    ridgeSupport386_001 ridgeSupport386_suffix_002 ridgeSupport386_001_decode ridgeSupport386_suffix_decode_002
theorem ridgeSupport386_suffix_decode_000 : PackedRawNatGrowth.readList 14 402 ridgeSupport386_rest_000 =
    (ridgeSupport386_suffix_000, ridgeSupport386_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 370
    ridgeSupport386_rest_000 ridgeSupport386_rest_001 ridgeSupport386_rest_013
    ridgeSupport386_000 ridgeSupport386_suffix_001 ridgeSupport386_000_decode ridgeSupport386_suffix_decode_001
theorem ridgeSupport386_eq : candidateRows 386 = ridgeSupport386_suffix_000 := by
  change candidateSupports 386 = ridgeSupport386_suffix_000
  rw [ridgeSupport386_source]
  exact congrArg Prod.fst ridgeSupport386_suffix_decode_000
theorem ridgeTest_large_386 : ridgeTest 386 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport386_eq]
    simp only [ridgeSupport386_suffix_000, ridgeSupport386_suffix_001, ridgeSupport386_suffix_002, ridgeSupport386_suffix_003, ridgeSupport386_suffix_004, ridgeSupport386_suffix_005, ridgeSupport386_suffix_006, ridgeSupport386_suffix_007, ridgeSupport386_suffix_008, ridgeSupport386_suffix_009, ridgeSupport386_suffix_010, ridgeSupport386_suffix_011, ridgeSupport386_suffix_012, ridgeSupport386_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport386_000_mask, ridgeSupport386_001_mask, ridgeSupport386_002_mask, ridgeSupport386_003_mask, ridgeSupport386_004_mask, ridgeSupport386_005_mask, ridgeSupport386_006_mask, ridgeSupport386_007_mask, ridgeSupport386_008_mask, ridgeSupport386_009_mask, ridgeSupport386_010_mask, ridgeSupport386_011_mask, ridgeSupport386_012_mask]
    decide +kernel
  · rw [ridgeSupport386_eq]
    simp only [ridgeSupport386_suffix_000, ridgeSupport386_suffix_001, ridgeSupport386_suffix_002, ridgeSupport386_suffix_003, ridgeSupport386_suffix_004, ridgeSupport386_suffix_005, ridgeSupport386_suffix_006, ridgeSupport386_suffix_007, ridgeSupport386_suffix_008, ridgeSupport386_suffix_009, ridgeSupport386_suffix_010, ridgeSupport386_suffix_011, ridgeSupport386_suffix_012, ridgeSupport386_suffix_013, List.all_append, List.all_nil, ridgeSupport386_000_checked, ridgeSupport386_001_checked, ridgeSupport386_002_checked, ridgeSupport386_003_checked, ridgeSupport386_004_checked, ridgeSupport386_005_checked, ridgeSupport386_006_checked, ridgeSupport386_007_checked, ridgeSupport386_008_checked, ridgeSupport386_009_checked, ridgeSupport386_010_checked, ridgeSupport386_011_checked, ridgeSupport386_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
