module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport208PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 208 023 14
cert_ridgeSupport_suffix_decode_2 208 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 208 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 208 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 208 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 208 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 208 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 208 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 208 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 208 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 208 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 208 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 208 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 208 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 208 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 208 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 208 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 208 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 208 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 208 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 208 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 208 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 208 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 208 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 208
theorem ridgeTest_large_208 : ridgeTest 208 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport208_eq]
    simp only [ridgeSupport208_suffix_000, ridgeSupport208_suffix_001, ridgeSupport208_suffix_002, ridgeSupport208_suffix_003, ridgeSupport208_suffix_004, ridgeSupport208_suffix_005, ridgeSupport208_suffix_006, ridgeSupport208_suffix_007, ridgeSupport208_suffix_008, ridgeSupport208_suffix_009, ridgeSupport208_suffix_010, ridgeSupport208_suffix_011, ridgeSupport208_suffix_012, ridgeSupport208_suffix_013, ridgeSupport208_suffix_014, ridgeSupport208_suffix_015, ridgeSupport208_suffix_016, ridgeSupport208_suffix_017, ridgeSupport208_suffix_018, ridgeSupport208_suffix_019, ridgeSupport208_suffix_020, ridgeSupport208_suffix_021, ridgeSupport208_suffix_022, ridgeSupport208_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport208_000_mask, ridgeSupport208_001_mask, ridgeSupport208_002_mask, ridgeSupport208_003_mask, ridgeSupport208_004_mask, ridgeSupport208_005_mask, ridgeSupport208_006_mask, ridgeSupport208_007_mask, ridgeSupport208_008_mask, ridgeSupport208_009_mask, ridgeSupport208_010_mask, ridgeSupport208_011_mask, ridgeSupport208_012_mask, ridgeSupport208_013_mask, ridgeSupport208_014_mask, ridgeSupport208_015_mask, ridgeSupport208_016_mask, ridgeSupport208_017_mask, ridgeSupport208_018_mask, ridgeSupport208_019_mask, ridgeSupport208_020_mask, ridgeSupport208_021_mask, ridgeSupport208_022_mask]
    decide +kernel
  · rw [ridgeSupport208_eq]
    simp only [ridgeSupport208_suffix_000, ridgeSupport208_suffix_001, ridgeSupport208_suffix_002, ridgeSupport208_suffix_003, ridgeSupport208_suffix_004, ridgeSupport208_suffix_005, ridgeSupport208_suffix_006, ridgeSupport208_suffix_007, ridgeSupport208_suffix_008, ridgeSupport208_suffix_009, ridgeSupport208_suffix_010, ridgeSupport208_suffix_011, ridgeSupport208_suffix_012, ridgeSupport208_suffix_013, ridgeSupport208_suffix_014, ridgeSupport208_suffix_015, ridgeSupport208_suffix_016, ridgeSupport208_suffix_017, ridgeSupport208_suffix_018, ridgeSupport208_suffix_019, ridgeSupport208_suffix_020, ridgeSupport208_suffix_021, ridgeSupport208_suffix_022, ridgeSupport208_suffix_023, List.all_append, List.all_nil, ridgeSupport208_000_checked, ridgeSupport208_001_checked, ridgeSupport208_002_checked, ridgeSupport208_003_checked, ridgeSupport208_004_checked, ridgeSupport208_005_checked, ridgeSupport208_006_checked, ridgeSupport208_007_checked, ridgeSupport208_008_checked, ridgeSupport208_009_checked, ridgeSupport208_010_checked, ridgeSupport208_011_checked, ridgeSupport208_012_checked, ridgeSupport208_013_checked, ridgeSupport208_014_checked, ridgeSupport208_015_checked, ridgeSupport208_016_checked, ridgeSupport208_017_checked, ridgeSupport208_018_checked, ridgeSupport208_019_checked, ridgeSupport208_020_checked, ridgeSupport208_021_checked, ridgeSupport208_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
