module
prelude
public import RootedSixExtra05GrowthCacheRidgeSupport448Part000
public import RootedSixExtra05GrowthCacheRidgeSupport448Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport448_suffix_decode_012 : PackedRawNatGrowth.readList 12 0 ridgeSupport448_rest_012 =
    (ridgeSupport448_suffix_012, ridgeSupport448_rest_012) := by rfl
theorem ridgeSupport448_suffix_decode_011 : PackedRawNatGrowth.readList 12 9 ridgeSupport448_rest_011 =
    (ridgeSupport448_suffix_011, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 9 0
    ridgeSupport448_rest_011 ridgeSupport448_rest_012 ridgeSupport448_rest_012
    ridgeSupport448_011 ridgeSupport448_suffix_012 ridgeSupport448_011_decode ridgeSupport448_suffix_decode_012
theorem ridgeSupport448_suffix_decode_010 : PackedRawNatGrowth.readList 12 41 ridgeSupport448_rest_010 =
    (ridgeSupport448_suffix_010, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 9
    ridgeSupport448_rest_010 ridgeSupport448_rest_011 ridgeSupport448_rest_012
    ridgeSupport448_010 ridgeSupport448_suffix_011 ridgeSupport448_010_decode ridgeSupport448_suffix_decode_011
theorem ridgeSupport448_suffix_decode_009 : PackedRawNatGrowth.readList 12 73 ridgeSupport448_rest_009 =
    (ridgeSupport448_suffix_009, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 41
    ridgeSupport448_rest_009 ridgeSupport448_rest_010 ridgeSupport448_rest_012
    ridgeSupport448_009 ridgeSupport448_suffix_010 ridgeSupport448_009_decode ridgeSupport448_suffix_decode_010
theorem ridgeSupport448_suffix_decode_008 : PackedRawNatGrowth.readList 12 105 ridgeSupport448_rest_008 =
    (ridgeSupport448_suffix_008, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 73
    ridgeSupport448_rest_008 ridgeSupport448_rest_009 ridgeSupport448_rest_012
    ridgeSupport448_008 ridgeSupport448_suffix_009 ridgeSupport448_008_decode ridgeSupport448_suffix_decode_009
theorem ridgeSupport448_suffix_decode_007 : PackedRawNatGrowth.readList 12 137 ridgeSupport448_rest_007 =
    (ridgeSupport448_suffix_007, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 105
    ridgeSupport448_rest_007 ridgeSupport448_rest_008 ridgeSupport448_rest_012
    ridgeSupport448_007 ridgeSupport448_suffix_008 ridgeSupport448_007_decode ridgeSupport448_suffix_decode_008
theorem ridgeSupport448_suffix_decode_006 : PackedRawNatGrowth.readList 12 169 ridgeSupport448_rest_006 =
    (ridgeSupport448_suffix_006, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 137
    ridgeSupport448_rest_006 ridgeSupport448_rest_007 ridgeSupport448_rest_012
    ridgeSupport448_006 ridgeSupport448_suffix_007 ridgeSupport448_006_decode ridgeSupport448_suffix_decode_007
theorem ridgeSupport448_suffix_decode_005 : PackedRawNatGrowth.readList 12 201 ridgeSupport448_rest_005 =
    (ridgeSupport448_suffix_005, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 169
    ridgeSupport448_rest_005 ridgeSupport448_rest_006 ridgeSupport448_rest_012
    ridgeSupport448_005 ridgeSupport448_suffix_006 ridgeSupport448_005_decode ridgeSupport448_suffix_decode_006
theorem ridgeSupport448_suffix_decode_004 : PackedRawNatGrowth.readList 12 233 ridgeSupport448_rest_004 =
    (ridgeSupport448_suffix_004, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 201
    ridgeSupport448_rest_004 ridgeSupport448_rest_005 ridgeSupport448_rest_012
    ridgeSupport448_004 ridgeSupport448_suffix_005 ridgeSupport448_004_decode ridgeSupport448_suffix_decode_005
theorem ridgeSupport448_suffix_decode_003 : PackedRawNatGrowth.readList 12 265 ridgeSupport448_rest_003 =
    (ridgeSupport448_suffix_003, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 233
    ridgeSupport448_rest_003 ridgeSupport448_rest_004 ridgeSupport448_rest_012
    ridgeSupport448_003 ridgeSupport448_suffix_004 ridgeSupport448_003_decode ridgeSupport448_suffix_decode_004
theorem ridgeSupport448_suffix_decode_002 : PackedRawNatGrowth.readList 12 297 ridgeSupport448_rest_002 =
    (ridgeSupport448_suffix_002, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 265
    ridgeSupport448_rest_002 ridgeSupport448_rest_003 ridgeSupport448_rest_012
    ridgeSupport448_002 ridgeSupport448_suffix_003 ridgeSupport448_002_decode ridgeSupport448_suffix_decode_003
theorem ridgeSupport448_suffix_decode_001 : PackedRawNatGrowth.readList 12 329 ridgeSupport448_rest_001 =
    (ridgeSupport448_suffix_001, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 297
    ridgeSupport448_rest_001 ridgeSupport448_rest_002 ridgeSupport448_rest_012
    ridgeSupport448_001 ridgeSupport448_suffix_002 ridgeSupport448_001_decode ridgeSupport448_suffix_decode_002
theorem ridgeSupport448_suffix_decode_000 : PackedRawNatGrowth.readList 12 361 ridgeSupport448_rest_000 =
    (ridgeSupport448_suffix_000, ridgeSupport448_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 329
    ridgeSupport448_rest_000 ridgeSupport448_rest_001 ridgeSupport448_rest_012
    ridgeSupport448_000 ridgeSupport448_suffix_001 ridgeSupport448_000_decode ridgeSupport448_suffix_decode_001
theorem ridgeSupport448_eq : candidateRows 448 = ridgeSupport448_suffix_000 := by
  change candidateSupports 448 = ridgeSupport448_suffix_000
  rw [ridgeSupport448_source]
  exact congrArg Prod.fst ridgeSupport448_suffix_decode_000
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask]
    decide +kernel
  · rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
