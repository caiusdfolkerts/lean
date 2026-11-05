module
prelude
public import RootedSixExtra05GrowthCacheRidgeSupport832Part000
public import RootedSixExtra05GrowthCacheRidgeSupport832Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport832_suffix_decode_012 : PackedRawNatGrowth.readList 12 0 ridgeSupport832_rest_012 =
    (ridgeSupport832_suffix_012, ridgeSupport832_rest_012) := by rfl
theorem ridgeSupport832_suffix_decode_011 : PackedRawNatGrowth.readList 12 9 ridgeSupport832_rest_011 =
    (ridgeSupport832_suffix_011, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 9 0
    ridgeSupport832_rest_011 ridgeSupport832_rest_012 ridgeSupport832_rest_012
    ridgeSupport832_011 ridgeSupport832_suffix_012 ridgeSupport832_011_decode ridgeSupport832_suffix_decode_012
theorem ridgeSupport832_suffix_decode_010 : PackedRawNatGrowth.readList 12 41 ridgeSupport832_rest_010 =
    (ridgeSupport832_suffix_010, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 9
    ridgeSupport832_rest_010 ridgeSupport832_rest_011 ridgeSupport832_rest_012
    ridgeSupport832_010 ridgeSupport832_suffix_011 ridgeSupport832_010_decode ridgeSupport832_suffix_decode_011
theorem ridgeSupport832_suffix_decode_009 : PackedRawNatGrowth.readList 12 73 ridgeSupport832_rest_009 =
    (ridgeSupport832_suffix_009, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 41
    ridgeSupport832_rest_009 ridgeSupport832_rest_010 ridgeSupport832_rest_012
    ridgeSupport832_009 ridgeSupport832_suffix_010 ridgeSupport832_009_decode ridgeSupport832_suffix_decode_010
theorem ridgeSupport832_suffix_decode_008 : PackedRawNatGrowth.readList 12 105 ridgeSupport832_rest_008 =
    (ridgeSupport832_suffix_008, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 73
    ridgeSupport832_rest_008 ridgeSupport832_rest_009 ridgeSupport832_rest_012
    ridgeSupport832_008 ridgeSupport832_suffix_009 ridgeSupport832_008_decode ridgeSupport832_suffix_decode_009
theorem ridgeSupport832_suffix_decode_007 : PackedRawNatGrowth.readList 12 137 ridgeSupport832_rest_007 =
    (ridgeSupport832_suffix_007, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 105
    ridgeSupport832_rest_007 ridgeSupport832_rest_008 ridgeSupport832_rest_012
    ridgeSupport832_007 ridgeSupport832_suffix_008 ridgeSupport832_007_decode ridgeSupport832_suffix_decode_008
theorem ridgeSupport832_suffix_decode_006 : PackedRawNatGrowth.readList 12 169 ridgeSupport832_rest_006 =
    (ridgeSupport832_suffix_006, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 137
    ridgeSupport832_rest_006 ridgeSupport832_rest_007 ridgeSupport832_rest_012
    ridgeSupport832_006 ridgeSupport832_suffix_007 ridgeSupport832_006_decode ridgeSupport832_suffix_decode_007
theorem ridgeSupport832_suffix_decode_005 : PackedRawNatGrowth.readList 12 201 ridgeSupport832_rest_005 =
    (ridgeSupport832_suffix_005, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 169
    ridgeSupport832_rest_005 ridgeSupport832_rest_006 ridgeSupport832_rest_012
    ridgeSupport832_005 ridgeSupport832_suffix_006 ridgeSupport832_005_decode ridgeSupport832_suffix_decode_006
theorem ridgeSupport832_suffix_decode_004 : PackedRawNatGrowth.readList 12 233 ridgeSupport832_rest_004 =
    (ridgeSupport832_suffix_004, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 201
    ridgeSupport832_rest_004 ridgeSupport832_rest_005 ridgeSupport832_rest_012
    ridgeSupport832_004 ridgeSupport832_suffix_005 ridgeSupport832_004_decode ridgeSupport832_suffix_decode_005
theorem ridgeSupport832_suffix_decode_003 : PackedRawNatGrowth.readList 12 265 ridgeSupport832_rest_003 =
    (ridgeSupport832_suffix_003, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 233
    ridgeSupport832_rest_003 ridgeSupport832_rest_004 ridgeSupport832_rest_012
    ridgeSupport832_003 ridgeSupport832_suffix_004 ridgeSupport832_003_decode ridgeSupport832_suffix_decode_004
theorem ridgeSupport832_suffix_decode_002 : PackedRawNatGrowth.readList 12 297 ridgeSupport832_rest_002 =
    (ridgeSupport832_suffix_002, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 265
    ridgeSupport832_rest_002 ridgeSupport832_rest_003 ridgeSupport832_rest_012
    ridgeSupport832_002 ridgeSupport832_suffix_003 ridgeSupport832_002_decode ridgeSupport832_suffix_decode_003
theorem ridgeSupport832_suffix_decode_001 : PackedRawNatGrowth.readList 12 329 ridgeSupport832_rest_001 =
    (ridgeSupport832_suffix_001, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 297
    ridgeSupport832_rest_001 ridgeSupport832_rest_002 ridgeSupport832_rest_012
    ridgeSupport832_001 ridgeSupport832_suffix_002 ridgeSupport832_001_decode ridgeSupport832_suffix_decode_002
theorem ridgeSupport832_suffix_decode_000 : PackedRawNatGrowth.readList 12 361 ridgeSupport832_rest_000 =
    (ridgeSupport832_suffix_000, ridgeSupport832_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 329
    ridgeSupport832_rest_000 ridgeSupport832_rest_001 ridgeSupport832_rest_012
    ridgeSupport832_000 ridgeSupport832_suffix_001 ridgeSupport832_000_decode ridgeSupport832_suffix_decode_001
theorem ridgeSupport832_eq : candidateRows 832 = ridgeSupport832_suffix_000 := by
  change candidateSupports 832 = ridgeSupport832_suffix_000
  rw [ridgeSupport832_source]
  exact congrArg Prod.fst ridgeSupport832_suffix_decode_000
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask, ridgeSupport832_010_mask, ridgeSupport832_011_mask]
    decide +kernel
  · rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, ridgeSupport832_010_checked, ridgeSupport832_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
