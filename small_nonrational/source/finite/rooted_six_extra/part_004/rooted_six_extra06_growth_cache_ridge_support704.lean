module
prelude
public import RootedSixExtra06GrowthCacheRidgeSupport704Part000
public import RootedSixExtra06GrowthCacheRidgeSupport704Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport704_suffix_decode_010 : PackedRawNatGrowth.readList 12 0 ridgeSupport704_rest_010 =
    (ridgeSupport704_suffix_010, ridgeSupport704_rest_010) := by rfl
theorem ridgeSupport704_suffix_decode_009 : PackedRawNatGrowth.readList 12 31 ridgeSupport704_rest_009 =
    (ridgeSupport704_suffix_009, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 31 0
    ridgeSupport704_rest_009 ridgeSupport704_rest_010 ridgeSupport704_rest_010
    ridgeSupport704_009 ridgeSupport704_suffix_010 ridgeSupport704_009_decode ridgeSupport704_suffix_decode_010
theorem ridgeSupport704_suffix_decode_008 : PackedRawNatGrowth.readList 12 63 ridgeSupport704_rest_008 =
    (ridgeSupport704_suffix_008, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 31
    ridgeSupport704_rest_008 ridgeSupport704_rest_009 ridgeSupport704_rest_010
    ridgeSupport704_008 ridgeSupport704_suffix_009 ridgeSupport704_008_decode ridgeSupport704_suffix_decode_009
theorem ridgeSupport704_suffix_decode_007 : PackedRawNatGrowth.readList 12 95 ridgeSupport704_rest_007 =
    (ridgeSupport704_suffix_007, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 63
    ridgeSupport704_rest_007 ridgeSupport704_rest_008 ridgeSupport704_rest_010
    ridgeSupport704_007 ridgeSupport704_suffix_008 ridgeSupport704_007_decode ridgeSupport704_suffix_decode_008
theorem ridgeSupport704_suffix_decode_006 : PackedRawNatGrowth.readList 12 127 ridgeSupport704_rest_006 =
    (ridgeSupport704_suffix_006, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 95
    ridgeSupport704_rest_006 ridgeSupport704_rest_007 ridgeSupport704_rest_010
    ridgeSupport704_006 ridgeSupport704_suffix_007 ridgeSupport704_006_decode ridgeSupport704_suffix_decode_007
theorem ridgeSupport704_suffix_decode_005 : PackedRawNatGrowth.readList 12 159 ridgeSupport704_rest_005 =
    (ridgeSupport704_suffix_005, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 127
    ridgeSupport704_rest_005 ridgeSupport704_rest_006 ridgeSupport704_rest_010
    ridgeSupport704_005 ridgeSupport704_suffix_006 ridgeSupport704_005_decode ridgeSupport704_suffix_decode_006
theorem ridgeSupport704_suffix_decode_004 : PackedRawNatGrowth.readList 12 191 ridgeSupport704_rest_004 =
    (ridgeSupport704_suffix_004, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 159
    ridgeSupport704_rest_004 ridgeSupport704_rest_005 ridgeSupport704_rest_010
    ridgeSupport704_004 ridgeSupport704_suffix_005 ridgeSupport704_004_decode ridgeSupport704_suffix_decode_005
theorem ridgeSupport704_suffix_decode_003 : PackedRawNatGrowth.readList 12 223 ridgeSupport704_rest_003 =
    (ridgeSupport704_suffix_003, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 191
    ridgeSupport704_rest_003 ridgeSupport704_rest_004 ridgeSupport704_rest_010
    ridgeSupport704_003 ridgeSupport704_suffix_004 ridgeSupport704_003_decode ridgeSupport704_suffix_decode_004
theorem ridgeSupport704_suffix_decode_002 : PackedRawNatGrowth.readList 12 255 ridgeSupport704_rest_002 =
    (ridgeSupport704_suffix_002, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 223
    ridgeSupport704_rest_002 ridgeSupport704_rest_003 ridgeSupport704_rest_010
    ridgeSupport704_002 ridgeSupport704_suffix_003 ridgeSupport704_002_decode ridgeSupport704_suffix_decode_003
theorem ridgeSupport704_suffix_decode_001 : PackedRawNatGrowth.readList 12 287 ridgeSupport704_rest_001 =
    (ridgeSupport704_suffix_001, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 255
    ridgeSupport704_rest_001 ridgeSupport704_rest_002 ridgeSupport704_rest_010
    ridgeSupport704_001 ridgeSupport704_suffix_002 ridgeSupport704_001_decode ridgeSupport704_suffix_decode_002
theorem ridgeSupport704_suffix_decode_000 : PackedRawNatGrowth.readList 12 319 ridgeSupport704_rest_000 =
    (ridgeSupport704_suffix_000, ridgeSupport704_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 287
    ridgeSupport704_rest_000 ridgeSupport704_rest_001 ridgeSupport704_rest_010
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
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask]
    decide +kernel
  · rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
