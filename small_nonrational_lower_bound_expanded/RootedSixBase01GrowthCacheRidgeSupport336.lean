module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport336PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 336 023 14
cert_ridgeSupport_suffix_decode_2 336 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 336 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 336 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 336 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 336 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 336 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 336 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 336 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 336 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 336 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 336 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 336 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 336 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 336 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 336 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 336 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 336 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 336 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 336 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 336 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 336 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 336 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 336 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 336
theorem ridgeTest_large_336 : ridgeTest 336 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport336_eq]
    simp only [ridgeSupport336_suffix_000, ridgeSupport336_suffix_001, ridgeSupport336_suffix_002, ridgeSupport336_suffix_003, ridgeSupport336_suffix_004, ridgeSupport336_suffix_005, ridgeSupport336_suffix_006, ridgeSupport336_suffix_007, ridgeSupport336_suffix_008, ridgeSupport336_suffix_009, ridgeSupport336_suffix_010, ridgeSupport336_suffix_011, ridgeSupport336_suffix_012, ridgeSupport336_suffix_013, ridgeSupport336_suffix_014, ridgeSupport336_suffix_015, ridgeSupport336_suffix_016, ridgeSupport336_suffix_017, ridgeSupport336_suffix_018, ridgeSupport336_suffix_019, ridgeSupport336_suffix_020, ridgeSupport336_suffix_021, ridgeSupport336_suffix_022, ridgeSupport336_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport336_000_mask, ridgeSupport336_001_mask, ridgeSupport336_002_mask, ridgeSupport336_003_mask, ridgeSupport336_004_mask, ridgeSupport336_005_mask, ridgeSupport336_006_mask, ridgeSupport336_007_mask, ridgeSupport336_008_mask, ridgeSupport336_009_mask, ridgeSupport336_010_mask, ridgeSupport336_011_mask, ridgeSupport336_012_mask, ridgeSupport336_013_mask, ridgeSupport336_014_mask, ridgeSupport336_015_mask, ridgeSupport336_016_mask, ridgeSupport336_017_mask, ridgeSupport336_018_mask, ridgeSupport336_019_mask, ridgeSupport336_020_mask, ridgeSupport336_021_mask, ridgeSupport336_022_mask]
    decide +kernel
  · rw [ridgeSupport336_eq]
    simp only [ridgeSupport336_suffix_000, ridgeSupport336_suffix_001, ridgeSupport336_suffix_002, ridgeSupport336_suffix_003, ridgeSupport336_suffix_004, ridgeSupport336_suffix_005, ridgeSupport336_suffix_006, ridgeSupport336_suffix_007, ridgeSupport336_suffix_008, ridgeSupport336_suffix_009, ridgeSupport336_suffix_010, ridgeSupport336_suffix_011, ridgeSupport336_suffix_012, ridgeSupport336_suffix_013, ridgeSupport336_suffix_014, ridgeSupport336_suffix_015, ridgeSupport336_suffix_016, ridgeSupport336_suffix_017, ridgeSupport336_suffix_018, ridgeSupport336_suffix_019, ridgeSupport336_suffix_020, ridgeSupport336_suffix_021, ridgeSupport336_suffix_022, ridgeSupport336_suffix_023, List.all_append, List.all_nil, ridgeSupport336_000_checked, ridgeSupport336_001_checked, ridgeSupport336_002_checked, ridgeSupport336_003_checked, ridgeSupport336_004_checked, ridgeSupport336_005_checked, ridgeSupport336_006_checked, ridgeSupport336_007_checked, ridgeSupport336_008_checked, ridgeSupport336_009_checked, ridgeSupport336_010_checked, ridgeSupport336_011_checked, ridgeSupport336_012_checked, ridgeSupport336_013_checked, ridgeSupport336_014_checked, ridgeSupport336_015_checked, ridgeSupport336_016_checked, ridgeSupport336_017_checked, ridgeSupport336_018_checked, ridgeSupport336_019_checked, ridgeSupport336_020_checked, ridgeSupport336_021_checked, ridgeSupport336_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
