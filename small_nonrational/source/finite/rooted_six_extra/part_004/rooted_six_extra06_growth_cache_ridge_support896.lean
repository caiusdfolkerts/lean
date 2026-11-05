module
prelude
public import RootedSixExtra06GrowthCacheRidgeSupport896Part000
public import RootedSixExtra06GrowthCacheRidgeSupport896Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport896_suffix_decode_010 : PackedRawNatGrowth.readList 12 0 ridgeSupport896_rest_010 =
    (ridgeSupport896_suffix_010, ridgeSupport896_rest_010) := by rfl
theorem ridgeSupport896_suffix_decode_009 : PackedRawNatGrowth.readList 12 31 ridgeSupport896_rest_009 =
    (ridgeSupport896_suffix_009, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 31 0
    ridgeSupport896_rest_009 ridgeSupport896_rest_010 ridgeSupport896_rest_010
    ridgeSupport896_009 ridgeSupport896_suffix_010 ridgeSupport896_009_decode ridgeSupport896_suffix_decode_010
theorem ridgeSupport896_suffix_decode_008 : PackedRawNatGrowth.readList 12 63 ridgeSupport896_rest_008 =
    (ridgeSupport896_suffix_008, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 31
    ridgeSupport896_rest_008 ridgeSupport896_rest_009 ridgeSupport896_rest_010
    ridgeSupport896_008 ridgeSupport896_suffix_009 ridgeSupport896_008_decode ridgeSupport896_suffix_decode_009
theorem ridgeSupport896_suffix_decode_007 : PackedRawNatGrowth.readList 12 95 ridgeSupport896_rest_007 =
    (ridgeSupport896_suffix_007, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 63
    ridgeSupport896_rest_007 ridgeSupport896_rest_008 ridgeSupport896_rest_010
    ridgeSupport896_007 ridgeSupport896_suffix_008 ridgeSupport896_007_decode ridgeSupport896_suffix_decode_008
theorem ridgeSupport896_suffix_decode_006 : PackedRawNatGrowth.readList 12 127 ridgeSupport896_rest_006 =
    (ridgeSupport896_suffix_006, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 95
    ridgeSupport896_rest_006 ridgeSupport896_rest_007 ridgeSupport896_rest_010
    ridgeSupport896_006 ridgeSupport896_suffix_007 ridgeSupport896_006_decode ridgeSupport896_suffix_decode_007
theorem ridgeSupport896_suffix_decode_005 : PackedRawNatGrowth.readList 12 159 ridgeSupport896_rest_005 =
    (ridgeSupport896_suffix_005, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 127
    ridgeSupport896_rest_005 ridgeSupport896_rest_006 ridgeSupport896_rest_010
    ridgeSupport896_005 ridgeSupport896_suffix_006 ridgeSupport896_005_decode ridgeSupport896_suffix_decode_006
theorem ridgeSupport896_suffix_decode_004 : PackedRawNatGrowth.readList 12 191 ridgeSupport896_rest_004 =
    (ridgeSupport896_suffix_004, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 159
    ridgeSupport896_rest_004 ridgeSupport896_rest_005 ridgeSupport896_rest_010
    ridgeSupport896_004 ridgeSupport896_suffix_005 ridgeSupport896_004_decode ridgeSupport896_suffix_decode_005
theorem ridgeSupport896_suffix_decode_003 : PackedRawNatGrowth.readList 12 223 ridgeSupport896_rest_003 =
    (ridgeSupport896_suffix_003, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 191
    ridgeSupport896_rest_003 ridgeSupport896_rest_004 ridgeSupport896_rest_010
    ridgeSupport896_003 ridgeSupport896_suffix_004 ridgeSupport896_003_decode ridgeSupport896_suffix_decode_004
theorem ridgeSupport896_suffix_decode_002 : PackedRawNatGrowth.readList 12 255 ridgeSupport896_rest_002 =
    (ridgeSupport896_suffix_002, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 223
    ridgeSupport896_rest_002 ridgeSupport896_rest_003 ridgeSupport896_rest_010
    ridgeSupport896_002 ridgeSupport896_suffix_003 ridgeSupport896_002_decode ridgeSupport896_suffix_decode_003
theorem ridgeSupport896_suffix_decode_001 : PackedRawNatGrowth.readList 12 287 ridgeSupport896_rest_001 =
    (ridgeSupport896_suffix_001, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 255
    ridgeSupport896_rest_001 ridgeSupport896_rest_002 ridgeSupport896_rest_010
    ridgeSupport896_001 ridgeSupport896_suffix_002 ridgeSupport896_001_decode ridgeSupport896_suffix_decode_002
theorem ridgeSupport896_suffix_decode_000 : PackedRawNatGrowth.readList 12 319 ridgeSupport896_rest_000 =
    (ridgeSupport896_suffix_000, ridgeSupport896_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 287
    ridgeSupport896_rest_000 ridgeSupport896_rest_001 ridgeSupport896_rest_010
    ridgeSupport896_000 ridgeSupport896_suffix_001 ridgeSupport896_000_decode ridgeSupport896_suffix_decode_001
theorem ridgeSupport896_eq : candidateRows 896 = ridgeSupport896_suffix_000 := by
  change candidateSupports 896 = ridgeSupport896_suffix_000
  rw [ridgeSupport896_source]
  exact congrArg Prod.fst ridgeSupport896_suffix_decode_000
theorem ridgeTest_large_896 : ridgeTest 896 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport896_000_mask, ridgeSupport896_001_mask, ridgeSupport896_002_mask, ridgeSupport896_003_mask, ridgeSupport896_004_mask, ridgeSupport896_005_mask, ridgeSupport896_006_mask, ridgeSupport896_007_mask, ridgeSupport896_008_mask, ridgeSupport896_009_mask]
    decide +kernel
  · rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, List.all_append, List.all_nil, ridgeSupport896_000_checked, ridgeSupport896_001_checked, ridgeSupport896_002_checked, ridgeSupport896_003_checked, ridgeSupport896_004_checked, ridgeSupport896_005_checked, ridgeSupport896_006_checked, ridgeSupport896_007_checked, ridgeSupport896_008_checked, ridgeSupport896_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
