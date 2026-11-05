module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport584Part000
public import RootedSixExtra02GrowthCacheRidgeSupport584Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport584_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport584_rest_013 =
    (ridgeSupport584_suffix_013, ridgeSupport584_rest_013) := by rfl
theorem ridgeSupport584_suffix_decode_012 : PackedRawNatGrowth.readList 13 20 ridgeSupport584_rest_012 =
    (ridgeSupport584_suffix_012, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 20 0
    ridgeSupport584_rest_012 ridgeSupport584_rest_013 ridgeSupport584_rest_013
    ridgeSupport584_012 ridgeSupport584_suffix_013 ridgeSupport584_012_decode ridgeSupport584_suffix_decode_013
theorem ridgeSupport584_suffix_decode_011 : PackedRawNatGrowth.readList 13 52 ridgeSupport584_rest_011 =
    (ridgeSupport584_suffix_011, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 20
    ridgeSupport584_rest_011 ridgeSupport584_rest_012 ridgeSupport584_rest_013
    ridgeSupport584_011 ridgeSupport584_suffix_012 ridgeSupport584_011_decode ridgeSupport584_suffix_decode_012
theorem ridgeSupport584_suffix_decode_010 : PackedRawNatGrowth.readList 13 84 ridgeSupport584_rest_010 =
    (ridgeSupport584_suffix_010, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 52
    ridgeSupport584_rest_010 ridgeSupport584_rest_011 ridgeSupport584_rest_013
    ridgeSupport584_010 ridgeSupport584_suffix_011 ridgeSupport584_010_decode ridgeSupport584_suffix_decode_011
theorem ridgeSupport584_suffix_decode_009 : PackedRawNatGrowth.readList 13 116 ridgeSupport584_rest_009 =
    (ridgeSupport584_suffix_009, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 84
    ridgeSupport584_rest_009 ridgeSupport584_rest_010 ridgeSupport584_rest_013
    ridgeSupport584_009 ridgeSupport584_suffix_010 ridgeSupport584_009_decode ridgeSupport584_suffix_decode_010
theorem ridgeSupport584_suffix_decode_008 : PackedRawNatGrowth.readList 13 148 ridgeSupport584_rest_008 =
    (ridgeSupport584_suffix_008, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 116
    ridgeSupport584_rest_008 ridgeSupport584_rest_009 ridgeSupport584_rest_013
    ridgeSupport584_008 ridgeSupport584_suffix_009 ridgeSupport584_008_decode ridgeSupport584_suffix_decode_009
theorem ridgeSupport584_suffix_decode_007 : PackedRawNatGrowth.readList 13 180 ridgeSupport584_rest_007 =
    (ridgeSupport584_suffix_007, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 148
    ridgeSupport584_rest_007 ridgeSupport584_rest_008 ridgeSupport584_rest_013
    ridgeSupport584_007 ridgeSupport584_suffix_008 ridgeSupport584_007_decode ridgeSupport584_suffix_decode_008
theorem ridgeSupport584_suffix_decode_006 : PackedRawNatGrowth.readList 13 212 ridgeSupport584_rest_006 =
    (ridgeSupport584_suffix_006, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 180
    ridgeSupport584_rest_006 ridgeSupport584_rest_007 ridgeSupport584_rest_013
    ridgeSupport584_006 ridgeSupport584_suffix_007 ridgeSupport584_006_decode ridgeSupport584_suffix_decode_007
theorem ridgeSupport584_suffix_decode_005 : PackedRawNatGrowth.readList 13 244 ridgeSupport584_rest_005 =
    (ridgeSupport584_suffix_005, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 212
    ridgeSupport584_rest_005 ridgeSupport584_rest_006 ridgeSupport584_rest_013
    ridgeSupport584_005 ridgeSupport584_suffix_006 ridgeSupport584_005_decode ridgeSupport584_suffix_decode_006
theorem ridgeSupport584_suffix_decode_004 : PackedRawNatGrowth.readList 13 276 ridgeSupport584_rest_004 =
    (ridgeSupport584_suffix_004, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 244
    ridgeSupport584_rest_004 ridgeSupport584_rest_005 ridgeSupport584_rest_013
    ridgeSupport584_004 ridgeSupport584_suffix_005 ridgeSupport584_004_decode ridgeSupport584_suffix_decode_005
theorem ridgeSupport584_suffix_decode_003 : PackedRawNatGrowth.readList 13 308 ridgeSupport584_rest_003 =
    (ridgeSupport584_suffix_003, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 276
    ridgeSupport584_rest_003 ridgeSupport584_rest_004 ridgeSupport584_rest_013
    ridgeSupport584_003 ridgeSupport584_suffix_004 ridgeSupport584_003_decode ridgeSupport584_suffix_decode_004
theorem ridgeSupport584_suffix_decode_002 : PackedRawNatGrowth.readList 13 340 ridgeSupport584_rest_002 =
    (ridgeSupport584_suffix_002, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 308
    ridgeSupport584_rest_002 ridgeSupport584_rest_003 ridgeSupport584_rest_013
    ridgeSupport584_002 ridgeSupport584_suffix_003 ridgeSupport584_002_decode ridgeSupport584_suffix_decode_003
theorem ridgeSupport584_suffix_decode_001 : PackedRawNatGrowth.readList 13 372 ridgeSupport584_rest_001 =
    (ridgeSupport584_suffix_001, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 340
    ridgeSupport584_rest_001 ridgeSupport584_rest_002 ridgeSupport584_rest_013
    ridgeSupport584_001 ridgeSupport584_suffix_002 ridgeSupport584_001_decode ridgeSupport584_suffix_decode_002
theorem ridgeSupport584_suffix_decode_000 : PackedRawNatGrowth.readList 13 404 ridgeSupport584_rest_000 =
    (ridgeSupport584_suffix_000, ridgeSupport584_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 372
    ridgeSupport584_rest_000 ridgeSupport584_rest_001 ridgeSupport584_rest_013
    ridgeSupport584_000 ridgeSupport584_suffix_001 ridgeSupport584_000_decode ridgeSupport584_suffix_decode_001
theorem ridgeSupport584_eq : candidateRows 584 = ridgeSupport584_suffix_000 := by
  change candidateSupports 584 = ridgeSupport584_suffix_000
  rw [ridgeSupport584_source]
  exact congrArg Prod.fst ridgeSupport584_suffix_decode_000
theorem ridgeTest_large_584 : ridgeTest 584 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport584_eq]
    simp only [ridgeSupport584_suffix_000, ridgeSupport584_suffix_001, ridgeSupport584_suffix_002, ridgeSupport584_suffix_003, ridgeSupport584_suffix_004, ridgeSupport584_suffix_005, ridgeSupport584_suffix_006, ridgeSupport584_suffix_007, ridgeSupport584_suffix_008, ridgeSupport584_suffix_009, ridgeSupport584_suffix_010, ridgeSupport584_suffix_011, ridgeSupport584_suffix_012, ridgeSupport584_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport584_000_mask, ridgeSupport584_001_mask, ridgeSupport584_002_mask, ridgeSupport584_003_mask, ridgeSupport584_004_mask, ridgeSupport584_005_mask, ridgeSupport584_006_mask, ridgeSupport584_007_mask, ridgeSupport584_008_mask, ridgeSupport584_009_mask, ridgeSupport584_010_mask, ridgeSupport584_011_mask, ridgeSupport584_012_mask]
    decide +kernel
  · rw [ridgeSupport584_eq]
    simp only [ridgeSupport584_suffix_000, ridgeSupport584_suffix_001, ridgeSupport584_suffix_002, ridgeSupport584_suffix_003, ridgeSupport584_suffix_004, ridgeSupport584_suffix_005, ridgeSupport584_suffix_006, ridgeSupport584_suffix_007, ridgeSupport584_suffix_008, ridgeSupport584_suffix_009, ridgeSupport584_suffix_010, ridgeSupport584_suffix_011, ridgeSupport584_suffix_012, ridgeSupport584_suffix_013, List.all_append, List.all_nil, ridgeSupport584_000_checked, ridgeSupport584_001_checked, ridgeSupport584_002_checked, ridgeSupport584_003_checked, ridgeSupport584_004_checked, ridgeSupport584_005_checked, ridgeSupport584_006_checked, ridgeSupport584_007_checked, ridgeSupport584_008_checked, ridgeSupport584_009_checked, ridgeSupport584_010_checked, ridgeSupport584_011_checked, ridgeSupport584_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
