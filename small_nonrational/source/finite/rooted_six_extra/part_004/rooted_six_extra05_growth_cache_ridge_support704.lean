module
prelude
public import RootedSixExtra05GrowthCacheRidgeSupport704Part000
public import RootedSixExtra05GrowthCacheRidgeSupport704Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport704_suffix_decode_012 : PackedRawNatGrowth.readList 12 0 ridgeSupport704_rest_012 =
    (ridgeSupport704_suffix_012, ridgeSupport704_rest_012) := by rfl
theorem ridgeSupport704_suffix_decode_011 : PackedRawNatGrowth.readList 12 9 ridgeSupport704_rest_011 =
    (ridgeSupport704_suffix_011, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 9 0
    ridgeSupport704_rest_011 ridgeSupport704_rest_012 ridgeSupport704_rest_012
    ridgeSupport704_011 ridgeSupport704_suffix_012 ridgeSupport704_011_decode ridgeSupport704_suffix_decode_012
theorem ridgeSupport704_suffix_decode_010 : PackedRawNatGrowth.readList 12 41 ridgeSupport704_rest_010 =
    (ridgeSupport704_suffix_010, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 9
    ridgeSupport704_rest_010 ridgeSupport704_rest_011 ridgeSupport704_rest_012
    ridgeSupport704_010 ridgeSupport704_suffix_011 ridgeSupport704_010_decode ridgeSupport704_suffix_decode_011
theorem ridgeSupport704_suffix_decode_009 : PackedRawNatGrowth.readList 12 73 ridgeSupport704_rest_009 =
    (ridgeSupport704_suffix_009, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 41
    ridgeSupport704_rest_009 ridgeSupport704_rest_010 ridgeSupport704_rest_012
    ridgeSupport704_009 ridgeSupport704_suffix_010 ridgeSupport704_009_decode ridgeSupport704_suffix_decode_010
theorem ridgeSupport704_suffix_decode_008 : PackedRawNatGrowth.readList 12 105 ridgeSupport704_rest_008 =
    (ridgeSupport704_suffix_008, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 73
    ridgeSupport704_rest_008 ridgeSupport704_rest_009 ridgeSupport704_rest_012
    ridgeSupport704_008 ridgeSupport704_suffix_009 ridgeSupport704_008_decode ridgeSupport704_suffix_decode_009
theorem ridgeSupport704_suffix_decode_007 : PackedRawNatGrowth.readList 12 137 ridgeSupport704_rest_007 =
    (ridgeSupport704_suffix_007, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 105
    ridgeSupport704_rest_007 ridgeSupport704_rest_008 ridgeSupport704_rest_012
    ridgeSupport704_007 ridgeSupport704_suffix_008 ridgeSupport704_007_decode ridgeSupport704_suffix_decode_008
theorem ridgeSupport704_suffix_decode_006 : PackedRawNatGrowth.readList 12 169 ridgeSupport704_rest_006 =
    (ridgeSupport704_suffix_006, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 137
    ridgeSupport704_rest_006 ridgeSupport704_rest_007 ridgeSupport704_rest_012
    ridgeSupport704_006 ridgeSupport704_suffix_007 ridgeSupport704_006_decode ridgeSupport704_suffix_decode_007
theorem ridgeSupport704_suffix_decode_005 : PackedRawNatGrowth.readList 12 201 ridgeSupport704_rest_005 =
    (ridgeSupport704_suffix_005, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 169
    ridgeSupport704_rest_005 ridgeSupport704_rest_006 ridgeSupport704_rest_012
    ridgeSupport704_005 ridgeSupport704_suffix_006 ridgeSupport704_005_decode ridgeSupport704_suffix_decode_006
theorem ridgeSupport704_suffix_decode_004 : PackedRawNatGrowth.readList 12 233 ridgeSupport704_rest_004 =
    (ridgeSupport704_suffix_004, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 201
    ridgeSupport704_rest_004 ridgeSupport704_rest_005 ridgeSupport704_rest_012
    ridgeSupport704_004 ridgeSupport704_suffix_005 ridgeSupport704_004_decode ridgeSupport704_suffix_decode_005
theorem ridgeSupport704_suffix_decode_003 : PackedRawNatGrowth.readList 12 265 ridgeSupport704_rest_003 =
    (ridgeSupport704_suffix_003, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 233
    ridgeSupport704_rest_003 ridgeSupport704_rest_004 ridgeSupport704_rest_012
    ridgeSupport704_003 ridgeSupport704_suffix_004 ridgeSupport704_003_decode ridgeSupport704_suffix_decode_004
theorem ridgeSupport704_suffix_decode_002 : PackedRawNatGrowth.readList 12 297 ridgeSupport704_rest_002 =
    (ridgeSupport704_suffix_002, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 265
    ridgeSupport704_rest_002 ridgeSupport704_rest_003 ridgeSupport704_rest_012
    ridgeSupport704_002 ridgeSupport704_suffix_003 ridgeSupport704_002_decode ridgeSupport704_suffix_decode_003
theorem ridgeSupport704_suffix_decode_001 : PackedRawNatGrowth.readList 12 329 ridgeSupport704_rest_001 =
    (ridgeSupport704_suffix_001, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 297
    ridgeSupport704_rest_001 ridgeSupport704_rest_002 ridgeSupport704_rest_012
    ridgeSupport704_001 ridgeSupport704_suffix_002 ridgeSupport704_001_decode ridgeSupport704_suffix_decode_002
theorem ridgeSupport704_suffix_decode_000 : PackedRawNatGrowth.readList 12 361 ridgeSupport704_rest_000 =
    (ridgeSupport704_suffix_000, ridgeSupport704_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 329
    ridgeSupport704_rest_000 ridgeSupport704_rest_001 ridgeSupport704_rest_012
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
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask, ridgeSupport704_010_mask, ridgeSupport704_011_mask]
    decide +kernel
  · rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, ridgeSupport704_010_checked, ridgeSupport704_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
