module
prelude
public import RootedSixBase04GrowthCacheRidgeSupport704Part000
public import RootedSixBase04GrowthCacheRidgeSupport704Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport704_suffix_decode_015 : PackedRawNatGrowth.readList 12 0 ridgeSupport704_rest_015 =
    (ridgeSupport704_suffix_015, ridgeSupport704_rest_015) := by rfl
theorem ridgeSupport704_suffix_decode_014 : PackedRawNatGrowth.readList 12 15 ridgeSupport704_rest_014 =
    (ridgeSupport704_suffix_014, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 15 0
    ridgeSupport704_rest_014 ridgeSupport704_rest_015 ridgeSupport704_rest_015
    ridgeSupport704_014 ridgeSupport704_suffix_015 ridgeSupport704_014_decode ridgeSupport704_suffix_decode_015
theorem ridgeSupport704_suffix_decode_013 : PackedRawNatGrowth.readList 12 47 ridgeSupport704_rest_013 =
    (ridgeSupport704_suffix_013, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 15
    ridgeSupport704_rest_013 ridgeSupport704_rest_014 ridgeSupport704_rest_015
    ridgeSupport704_013 ridgeSupport704_suffix_014 ridgeSupport704_013_decode ridgeSupport704_suffix_decode_014
theorem ridgeSupport704_suffix_decode_012 : PackedRawNatGrowth.readList 12 79 ridgeSupport704_rest_012 =
    (ridgeSupport704_suffix_012, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 47
    ridgeSupport704_rest_012 ridgeSupport704_rest_013 ridgeSupport704_rest_015
    ridgeSupport704_012 ridgeSupport704_suffix_013 ridgeSupport704_012_decode ridgeSupport704_suffix_decode_013
theorem ridgeSupport704_suffix_decode_011 : PackedRawNatGrowth.readList 12 111 ridgeSupport704_rest_011 =
    (ridgeSupport704_suffix_011, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 79
    ridgeSupport704_rest_011 ridgeSupport704_rest_012 ridgeSupport704_rest_015
    ridgeSupport704_011 ridgeSupport704_suffix_012 ridgeSupport704_011_decode ridgeSupport704_suffix_decode_012
theorem ridgeSupport704_suffix_decode_010 : PackedRawNatGrowth.readList 12 143 ridgeSupport704_rest_010 =
    (ridgeSupport704_suffix_010, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 111
    ridgeSupport704_rest_010 ridgeSupport704_rest_011 ridgeSupport704_rest_015
    ridgeSupport704_010 ridgeSupport704_suffix_011 ridgeSupport704_010_decode ridgeSupport704_suffix_decode_011
theorem ridgeSupport704_suffix_decode_009 : PackedRawNatGrowth.readList 12 175 ridgeSupport704_rest_009 =
    (ridgeSupport704_suffix_009, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 143
    ridgeSupport704_rest_009 ridgeSupport704_rest_010 ridgeSupport704_rest_015
    ridgeSupport704_009 ridgeSupport704_suffix_010 ridgeSupport704_009_decode ridgeSupport704_suffix_decode_010
theorem ridgeSupport704_suffix_decode_008 : PackedRawNatGrowth.readList 12 207 ridgeSupport704_rest_008 =
    (ridgeSupport704_suffix_008, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 175
    ridgeSupport704_rest_008 ridgeSupport704_rest_009 ridgeSupport704_rest_015
    ridgeSupport704_008 ridgeSupport704_suffix_009 ridgeSupport704_008_decode ridgeSupport704_suffix_decode_009
theorem ridgeSupport704_suffix_decode_007 : PackedRawNatGrowth.readList 12 239 ridgeSupport704_rest_007 =
    (ridgeSupport704_suffix_007, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 207
    ridgeSupport704_rest_007 ridgeSupport704_rest_008 ridgeSupport704_rest_015
    ridgeSupport704_007 ridgeSupport704_suffix_008 ridgeSupport704_007_decode ridgeSupport704_suffix_decode_008
theorem ridgeSupport704_suffix_decode_006 : PackedRawNatGrowth.readList 12 271 ridgeSupport704_rest_006 =
    (ridgeSupport704_suffix_006, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 239
    ridgeSupport704_rest_006 ridgeSupport704_rest_007 ridgeSupport704_rest_015
    ridgeSupport704_006 ridgeSupport704_suffix_007 ridgeSupport704_006_decode ridgeSupport704_suffix_decode_007
theorem ridgeSupport704_suffix_decode_005 : PackedRawNatGrowth.readList 12 303 ridgeSupport704_rest_005 =
    (ridgeSupport704_suffix_005, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 271
    ridgeSupport704_rest_005 ridgeSupport704_rest_006 ridgeSupport704_rest_015
    ridgeSupport704_005 ridgeSupport704_suffix_006 ridgeSupport704_005_decode ridgeSupport704_suffix_decode_006
theorem ridgeSupport704_suffix_decode_004 : PackedRawNatGrowth.readList 12 335 ridgeSupport704_rest_004 =
    (ridgeSupport704_suffix_004, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 303
    ridgeSupport704_rest_004 ridgeSupport704_rest_005 ridgeSupport704_rest_015
    ridgeSupport704_004 ridgeSupport704_suffix_005 ridgeSupport704_004_decode ridgeSupport704_suffix_decode_005
theorem ridgeSupport704_suffix_decode_003 : PackedRawNatGrowth.readList 12 367 ridgeSupport704_rest_003 =
    (ridgeSupport704_suffix_003, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 335
    ridgeSupport704_rest_003 ridgeSupport704_rest_004 ridgeSupport704_rest_015
    ridgeSupport704_003 ridgeSupport704_suffix_004 ridgeSupport704_003_decode ridgeSupport704_suffix_decode_004
theorem ridgeSupport704_suffix_decode_002 : PackedRawNatGrowth.readList 12 399 ridgeSupport704_rest_002 =
    (ridgeSupport704_suffix_002, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 367
    ridgeSupport704_rest_002 ridgeSupport704_rest_003 ridgeSupport704_rest_015
    ridgeSupport704_002 ridgeSupport704_suffix_003 ridgeSupport704_002_decode ridgeSupport704_suffix_decode_003
theorem ridgeSupport704_suffix_decode_001 : PackedRawNatGrowth.readList 12 431 ridgeSupport704_rest_001 =
    (ridgeSupport704_suffix_001, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 399
    ridgeSupport704_rest_001 ridgeSupport704_rest_002 ridgeSupport704_rest_015
    ridgeSupport704_001 ridgeSupport704_suffix_002 ridgeSupport704_001_decode ridgeSupport704_suffix_decode_002
theorem ridgeSupport704_suffix_decode_000 : PackedRawNatGrowth.readList 12 463 ridgeSupport704_rest_000 =
    (ridgeSupport704_suffix_000, ridgeSupport704_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 431
    ridgeSupport704_rest_000 ridgeSupport704_rest_001 ridgeSupport704_rest_015
    ridgeSupport704_000 ridgeSupport704_suffix_001 ridgeSupport704_000_decode ridgeSupport704_suffix_decode_001
theorem ridgeSupport704_eq : candidateRows 704 = ridgeSupport704_suffix_000 := by
  change candidateSupports 704 = ridgeSupport704_suffix_000
  rw [ridgeSupport704_source]
  exact congrArg Prod.fst ridgeSupport704_suffix_decode_000
theorem ridgeTest_large_704 : ridgeTest 704 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask, ridgeSupport704_010_mask, ridgeSupport704_011_mask, ridgeSupport704_012_mask, ridgeSupport704_013_mask, ridgeSupport704_014_mask]
    decide +kernel
  · rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, ridgeSupport704_010_checked, ridgeSupport704_011_checked, ridgeSupport704_012_checked, ridgeSupport704_013_checked, ridgeSupport704_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase04
