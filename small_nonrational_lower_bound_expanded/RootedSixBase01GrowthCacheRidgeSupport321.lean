module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport321Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 321 026 14
cert_ridgeSupport_suffix_decode_2 321 025 14 15 15 026 026 0
cert_ridgeSupport_suffix_decode_2 321 024 14 47 32 026 025 15
cert_ridgeSupport_suffix_decode_2 321 023 14 79 32 026 024 47
cert_ridgeSupport_suffix_decode_2 321 022 14 111 32 026 023 79
cert_ridgeSupport_suffix_decode_2 321 021 14 143 32 026 022 111
cert_ridgeSupport_suffix_decode_2 321 020 14 175 32 026 021 143
cert_ridgeSupport_suffix_decode_2 321 019 14 207 32 026 020 175
cert_ridgeSupport_suffix_decode_2 321 018 14 239 32 026 019 207
cert_ridgeSupport_suffix_decode_2 321 017 14 271 32 026 018 239
cert_ridgeSupport_suffix_decode_2 321 016 14 303 32 026 017 271
cert_ridgeSupport_suffix_decode_2 321 015 14 335 32 026 016 303
cert_ridgeSupport_suffix_decode_2 321 014 14 367 32 026 015 335
cert_ridgeSupport_suffix_decode_2 321 013 14 399 32 026 014 367
cert_ridgeSupport_suffix_decode_2 321 012 14 431 32 026 013 399
cert_ridgeSupport_suffix_decode_2 321 011 14 463 32 026 012 431
cert_ridgeSupport_suffix_decode_2 321 010 14 495 32 026 011 463
cert_ridgeSupport_suffix_decode_2 321 009 14 527 32 026 010 495
cert_ridgeSupport_suffix_decode_2 321 008 14 559 32 026 009 527
cert_ridgeSupport_suffix_decode_2 321 007 14 591 32 026 008 559
cert_ridgeSupport_suffix_decode_2 321 006 14 623 32 026 007 591
cert_ridgeSupport_suffix_decode_2 321 005 14 655 32 026 006 623
cert_ridgeSupport_suffix_decode_2 321 004 14 687 32 026 005 655
cert_ridgeSupport_suffix_decode_2 321 003 14 719 32 026 004 687
cert_ridgeSupport_suffix_decode_2 321 002 14 751 32 026 003 719
cert_ridgeSupport_suffix_decode_2 321 001 14 783 32 026 002 751
cert_ridgeSupport_suffix_decode_2 321 000 14 815 32 026 001 783
cert_ridgeSupport_eq_3 321
theorem ridgeTest_large_321 : ridgeTest 321 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport321_eq]
    simp only [ridgeSupport321_suffix_000, ridgeSupport321_suffix_001, ridgeSupport321_suffix_002, ridgeSupport321_suffix_003, ridgeSupport321_suffix_004, ridgeSupport321_suffix_005, ridgeSupport321_suffix_006, ridgeSupport321_suffix_007, ridgeSupport321_suffix_008, ridgeSupport321_suffix_009, ridgeSupport321_suffix_010, ridgeSupport321_suffix_011, ridgeSupport321_suffix_012, ridgeSupport321_suffix_013, ridgeSupport321_suffix_014, ridgeSupport321_suffix_015, ridgeSupport321_suffix_016, ridgeSupport321_suffix_017, ridgeSupport321_suffix_018, ridgeSupport321_suffix_019, ridgeSupport321_suffix_020, ridgeSupport321_suffix_021, ridgeSupport321_suffix_022, ridgeSupport321_suffix_023, ridgeSupport321_suffix_024, ridgeSupport321_suffix_025, ridgeSupport321_suffix_026, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport321_000_mask, ridgeSupport321_001_mask, ridgeSupport321_002_mask, ridgeSupport321_003_mask, ridgeSupport321_004_mask, ridgeSupport321_005_mask, ridgeSupport321_006_mask, ridgeSupport321_007_mask, ridgeSupport321_008_mask, ridgeSupport321_009_mask, ridgeSupport321_010_mask, ridgeSupport321_011_mask, ridgeSupport321_012_mask, ridgeSupport321_013_mask, ridgeSupport321_014_mask, ridgeSupport321_015_mask, ridgeSupport321_016_mask, ridgeSupport321_017_mask, ridgeSupport321_018_mask, ridgeSupport321_019_mask, ridgeSupport321_020_mask, ridgeSupport321_021_mask, ridgeSupport321_022_mask, ridgeSupport321_023_mask, ridgeSupport321_024_mask, ridgeSupport321_025_mask]
    decide +kernel
  · rw [ridgeSupport321_eq]
    simp only [ridgeSupport321_suffix_000, ridgeSupport321_suffix_001, ridgeSupport321_suffix_002, ridgeSupport321_suffix_003, ridgeSupport321_suffix_004, ridgeSupport321_suffix_005, ridgeSupport321_suffix_006, ridgeSupport321_suffix_007, ridgeSupport321_suffix_008, ridgeSupport321_suffix_009, ridgeSupport321_suffix_010, ridgeSupport321_suffix_011, ridgeSupport321_suffix_012, ridgeSupport321_suffix_013, ridgeSupport321_suffix_014, ridgeSupport321_suffix_015, ridgeSupport321_suffix_016, ridgeSupport321_suffix_017, ridgeSupport321_suffix_018, ridgeSupport321_suffix_019, ridgeSupport321_suffix_020, ridgeSupport321_suffix_021, ridgeSupport321_suffix_022, ridgeSupport321_suffix_023, ridgeSupport321_suffix_024, ridgeSupport321_suffix_025, ridgeSupport321_suffix_026, List.all_append, List.all_nil, ridgeSupport321_000_checked, ridgeSupport321_001_checked, ridgeSupport321_002_checked, ridgeSupport321_003_checked, ridgeSupport321_004_checked, ridgeSupport321_005_checked, ridgeSupport321_006_checked, ridgeSupport321_007_checked, ridgeSupport321_008_checked, ridgeSupport321_009_checked, ridgeSupport321_010_checked, ridgeSupport321_011_checked, ridgeSupport321_012_checked, ridgeSupport321_013_checked, ridgeSupport321_014_checked, ridgeSupport321_015_checked, ridgeSupport321_016_checked, ridgeSupport321_017_checked, ridgeSupport321_018_checked, ridgeSupport321_019_checked, ridgeSupport321_020_checked, ridgeSupport321_021_checked, ridgeSupport321_022_checked, ridgeSupport321_023_checked, ridgeSupport321_024_checked, ridgeSupport321_025_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
