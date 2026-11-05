module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport134Part000
public import RootedSixExtra00GrowthCacheRidgeSupport134Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport134_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport134_rest_009 =
    (ridgeSupport134_suffix_009, ridgeSupport134_rest_009) := by rfl
theorem ridgeSupport134_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport134_rest_008 =
    (ridgeSupport134_suffix_008, ridgeSupport134_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport134_rest_008 ridgeSupport134_rest_009 ridgeSupport134_rest_009
    ridgeSupport134_008 ridgeSupport134_suffix_009 ridgeSupport134_008_decode ridgeSupport134_suffix_decode_009
theorem ridgeSupport134_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport134_rest_007 =
    (ridgeSupport134_suffix_007, ridgeSupport134_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport134_rest_007 ridgeSupport134_rest_008 ridgeSupport134_rest_009
    ridgeSupport134_007 ridgeSupport134_suffix_008 ridgeSupport134_007_decode ridgeSupport134_suffix_decode_008
theorem ridgeSupport134_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport134_rest_006 =
    (ridgeSupport134_suffix_006, ridgeSupport134_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport134_rest_006 ridgeSupport134_rest_007 ridgeSupport134_rest_009
    ridgeSupport134_006 ridgeSupport134_suffix_007 ridgeSupport134_006_decode ridgeSupport134_suffix_decode_007
theorem ridgeSupport134_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport134_rest_005 =
    (ridgeSupport134_suffix_005, ridgeSupport134_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport134_rest_005 ridgeSupport134_rest_006 ridgeSupport134_rest_009
    ridgeSupport134_005 ridgeSupport134_suffix_006 ridgeSupport134_005_decode ridgeSupport134_suffix_decode_006
theorem ridgeSupport134_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport134_rest_004 =
    (ridgeSupport134_suffix_004, ridgeSupport134_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport134_rest_004 ridgeSupport134_rest_005 ridgeSupport134_rest_009
    ridgeSupport134_004 ridgeSupport134_suffix_005 ridgeSupport134_004_decode ridgeSupport134_suffix_decode_005
theorem ridgeSupport134_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport134_rest_003 =
    (ridgeSupport134_suffix_003, ridgeSupport134_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport134_rest_003 ridgeSupport134_rest_004 ridgeSupport134_rest_009
    ridgeSupport134_003 ridgeSupport134_suffix_004 ridgeSupport134_003_decode ridgeSupport134_suffix_decode_004
theorem ridgeSupport134_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport134_rest_002 =
    (ridgeSupport134_suffix_002, ridgeSupport134_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport134_rest_002 ridgeSupport134_rest_003 ridgeSupport134_rest_009
    ridgeSupport134_002 ridgeSupport134_suffix_003 ridgeSupport134_002_decode ridgeSupport134_suffix_decode_003
theorem ridgeSupport134_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport134_rest_001 =
    (ridgeSupport134_suffix_001, ridgeSupport134_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport134_rest_001 ridgeSupport134_rest_002 ridgeSupport134_rest_009
    ridgeSupport134_001 ridgeSupport134_suffix_002 ridgeSupport134_001_decode ridgeSupport134_suffix_decode_002
theorem ridgeSupport134_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport134_rest_000 =
    (ridgeSupport134_suffix_000, ridgeSupport134_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport134_rest_000 ridgeSupport134_rest_001 ridgeSupport134_rest_009
    ridgeSupport134_000 ridgeSupport134_suffix_001 ridgeSupport134_000_decode ridgeSupport134_suffix_decode_001
theorem ridgeSupport134_eq : candidateRows 134 = ridgeSupport134_suffix_000 := by
  change candidateSupports 134 = ridgeSupport134_suffix_000
  rw [ridgeSupport134_source]
  exact congrArg Prod.fst ridgeSupport134_suffix_decode_000
theorem ridgeTest_large_134 : ridgeTest 134 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport134_eq]
    simp only [ridgeSupport134_suffix_000, ridgeSupport134_suffix_001, ridgeSupport134_suffix_002, ridgeSupport134_suffix_003, ridgeSupport134_suffix_004, ridgeSupport134_suffix_005, ridgeSupport134_suffix_006, ridgeSupport134_suffix_007, ridgeSupport134_suffix_008, ridgeSupport134_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport134_000_mask, ridgeSupport134_001_mask, ridgeSupport134_002_mask, ridgeSupport134_003_mask, ridgeSupport134_004_mask, ridgeSupport134_005_mask, ridgeSupport134_006_mask, ridgeSupport134_007_mask, ridgeSupport134_008_mask]
    decide +kernel
  · rw [ridgeSupport134_eq]
    simp only [ridgeSupport134_suffix_000, ridgeSupport134_suffix_001, ridgeSupport134_suffix_002, ridgeSupport134_suffix_003, ridgeSupport134_suffix_004, ridgeSupport134_suffix_005, ridgeSupport134_suffix_006, ridgeSupport134_suffix_007, ridgeSupport134_suffix_008, ridgeSupport134_suffix_009, List.all_append, List.all_nil, ridgeSupport134_000_checked, ridgeSupport134_001_checked, ridgeSupport134_002_checked, ridgeSupport134_003_checked, ridgeSupport134_004_checked, ridgeSupport134_005_checked, ridgeSupport134_006_checked, ridgeSupport134_007_checked, ridgeSupport134_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
