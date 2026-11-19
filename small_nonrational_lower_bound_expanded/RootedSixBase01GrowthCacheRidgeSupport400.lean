module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport400PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 400 023 14
cert_ridgeSupport_suffix_decode_2 400 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 400 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 400 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 400 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 400 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 400 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 400 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 400 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 400 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 400 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 400 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 400 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 400 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 400 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 400 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 400 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 400 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 400 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 400 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 400 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 400 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 400 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 400 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 400
theorem ridgeTest_large_400 : ridgeTest 400 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport400_eq]
    simp only [ridgeSupport400_suffix_000, ridgeSupport400_suffix_001, ridgeSupport400_suffix_002, ridgeSupport400_suffix_003, ridgeSupport400_suffix_004, ridgeSupport400_suffix_005, ridgeSupport400_suffix_006, ridgeSupport400_suffix_007, ridgeSupport400_suffix_008, ridgeSupport400_suffix_009, ridgeSupport400_suffix_010, ridgeSupport400_suffix_011, ridgeSupport400_suffix_012, ridgeSupport400_suffix_013, ridgeSupport400_suffix_014, ridgeSupport400_suffix_015, ridgeSupport400_suffix_016, ridgeSupport400_suffix_017, ridgeSupport400_suffix_018, ridgeSupport400_suffix_019, ridgeSupport400_suffix_020, ridgeSupport400_suffix_021, ridgeSupport400_suffix_022, ridgeSupport400_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport400_000_mask, ridgeSupport400_001_mask, ridgeSupport400_002_mask, ridgeSupport400_003_mask, ridgeSupport400_004_mask, ridgeSupport400_005_mask, ridgeSupport400_006_mask, ridgeSupport400_007_mask, ridgeSupport400_008_mask, ridgeSupport400_009_mask, ridgeSupport400_010_mask, ridgeSupport400_011_mask, ridgeSupport400_012_mask, ridgeSupport400_013_mask, ridgeSupport400_014_mask, ridgeSupport400_015_mask, ridgeSupport400_016_mask, ridgeSupport400_017_mask, ridgeSupport400_018_mask, ridgeSupport400_019_mask, ridgeSupport400_020_mask, ridgeSupport400_021_mask, ridgeSupport400_022_mask]
    decide +kernel
  · rw [ridgeSupport400_eq]
    simp only [ridgeSupport400_suffix_000, ridgeSupport400_suffix_001, ridgeSupport400_suffix_002, ridgeSupport400_suffix_003, ridgeSupport400_suffix_004, ridgeSupport400_suffix_005, ridgeSupport400_suffix_006, ridgeSupport400_suffix_007, ridgeSupport400_suffix_008, ridgeSupport400_suffix_009, ridgeSupport400_suffix_010, ridgeSupport400_suffix_011, ridgeSupport400_suffix_012, ridgeSupport400_suffix_013, ridgeSupport400_suffix_014, ridgeSupport400_suffix_015, ridgeSupport400_suffix_016, ridgeSupport400_suffix_017, ridgeSupport400_suffix_018, ridgeSupport400_suffix_019, ridgeSupport400_suffix_020, ridgeSupport400_suffix_021, ridgeSupport400_suffix_022, ridgeSupport400_suffix_023, List.all_append, List.all_nil, ridgeSupport400_000_checked, ridgeSupport400_001_checked, ridgeSupport400_002_checked, ridgeSupport400_003_checked, ridgeSupport400_004_checked, ridgeSupport400_005_checked, ridgeSupport400_006_checked, ridgeSupport400_007_checked, ridgeSupport400_008_checked, ridgeSupport400_009_checked, ridgeSupport400_010_checked, ridgeSupport400_011_checked, ridgeSupport400_012_checked, ridgeSupport400_013_checked, ridgeSupport400_014_checked, ridgeSupport400_015_checked, ridgeSupport400_016_checked, ridgeSupport400_017_checked, ridgeSupport400_018_checked, ridgeSupport400_019_checked, ridgeSupport400_020_checked, ridgeSupport400_021_checked, ridgeSupport400_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
