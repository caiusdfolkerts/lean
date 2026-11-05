module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport164Part000
public import RootedSixExtra00GrowthCacheRidgeSupport164Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport164_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport164_rest_009 =
    (ridgeSupport164_suffix_009, ridgeSupport164_rest_009) := by rfl
theorem ridgeSupport164_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport164_rest_008 =
    (ridgeSupport164_suffix_008, ridgeSupport164_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport164_rest_008 ridgeSupport164_rest_009 ridgeSupport164_rest_009
    ridgeSupport164_008 ridgeSupport164_suffix_009 ridgeSupport164_008_decode ridgeSupport164_suffix_decode_009
theorem ridgeSupport164_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport164_rest_007 =
    (ridgeSupport164_suffix_007, ridgeSupport164_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport164_rest_007 ridgeSupport164_rest_008 ridgeSupport164_rest_009
    ridgeSupport164_007 ridgeSupport164_suffix_008 ridgeSupport164_007_decode ridgeSupport164_suffix_decode_008
theorem ridgeSupport164_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport164_rest_006 =
    (ridgeSupport164_suffix_006, ridgeSupport164_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport164_rest_006 ridgeSupport164_rest_007 ridgeSupport164_rest_009
    ridgeSupport164_006 ridgeSupport164_suffix_007 ridgeSupport164_006_decode ridgeSupport164_suffix_decode_007
theorem ridgeSupport164_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport164_rest_005 =
    (ridgeSupport164_suffix_005, ridgeSupport164_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport164_rest_005 ridgeSupport164_rest_006 ridgeSupport164_rest_009
    ridgeSupport164_005 ridgeSupport164_suffix_006 ridgeSupport164_005_decode ridgeSupport164_suffix_decode_006
theorem ridgeSupport164_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport164_rest_004 =
    (ridgeSupport164_suffix_004, ridgeSupport164_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport164_rest_004 ridgeSupport164_rest_005 ridgeSupport164_rest_009
    ridgeSupport164_004 ridgeSupport164_suffix_005 ridgeSupport164_004_decode ridgeSupport164_suffix_decode_005
theorem ridgeSupport164_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport164_rest_003 =
    (ridgeSupport164_suffix_003, ridgeSupport164_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport164_rest_003 ridgeSupport164_rest_004 ridgeSupport164_rest_009
    ridgeSupport164_003 ridgeSupport164_suffix_004 ridgeSupport164_003_decode ridgeSupport164_suffix_decode_004
theorem ridgeSupport164_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport164_rest_002 =
    (ridgeSupport164_suffix_002, ridgeSupport164_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport164_rest_002 ridgeSupport164_rest_003 ridgeSupport164_rest_009
    ridgeSupport164_002 ridgeSupport164_suffix_003 ridgeSupport164_002_decode ridgeSupport164_suffix_decode_003
theorem ridgeSupport164_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport164_rest_001 =
    (ridgeSupport164_suffix_001, ridgeSupport164_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport164_rest_001 ridgeSupport164_rest_002 ridgeSupport164_rest_009
    ridgeSupport164_001 ridgeSupport164_suffix_002 ridgeSupport164_001_decode ridgeSupport164_suffix_decode_002
theorem ridgeSupport164_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport164_rest_000 =
    (ridgeSupport164_suffix_000, ridgeSupport164_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport164_rest_000 ridgeSupport164_rest_001 ridgeSupport164_rest_009
    ridgeSupport164_000 ridgeSupport164_suffix_001 ridgeSupport164_000_decode ridgeSupport164_suffix_decode_001
theorem ridgeSupport164_eq : candidateRows 164 = ridgeSupport164_suffix_000 := by
  change candidateSupports 164 = ridgeSupport164_suffix_000
  rw [ridgeSupport164_source]
  exact congrArg Prod.fst ridgeSupport164_suffix_decode_000
theorem ridgeTest_large_164 : ridgeTest 164 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport164_eq]
    simp only [ridgeSupport164_suffix_000, ridgeSupport164_suffix_001, ridgeSupport164_suffix_002, ridgeSupport164_suffix_003, ridgeSupport164_suffix_004, ridgeSupport164_suffix_005, ridgeSupport164_suffix_006, ridgeSupport164_suffix_007, ridgeSupport164_suffix_008, ridgeSupport164_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport164_000_mask, ridgeSupport164_001_mask, ridgeSupport164_002_mask, ridgeSupport164_003_mask, ridgeSupport164_004_mask, ridgeSupport164_005_mask, ridgeSupport164_006_mask, ridgeSupport164_007_mask, ridgeSupport164_008_mask]
    decide +kernel
  · rw [ridgeSupport164_eq]
    simp only [ridgeSupport164_suffix_000, ridgeSupport164_suffix_001, ridgeSupport164_suffix_002, ridgeSupport164_suffix_003, ridgeSupport164_suffix_004, ridgeSupport164_suffix_005, ridgeSupport164_suffix_006, ridgeSupport164_suffix_007, ridgeSupport164_suffix_008, ridgeSupport164_suffix_009, List.all_append, List.all_nil, ridgeSupport164_000_checked, ridgeSupport164_001_checked, ridgeSupport164_002_checked, ridgeSupport164_003_checked, ridgeSupport164_004_checked, ridgeSupport164_005_checked, ridgeSupport164_006_checked, ridgeSupport164_007_checked, ridgeSupport164_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
