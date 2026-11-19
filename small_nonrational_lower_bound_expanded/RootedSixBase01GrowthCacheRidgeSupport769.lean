module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport769Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 769 026 14
cert_ridgeSupport_suffix_decode_2 769 025 14 15 15 026 026 0
cert_ridgeSupport_suffix_decode_2 769 024 14 47 32 026 025 15
cert_ridgeSupport_suffix_decode_2 769 023 14 79 32 026 024 47
cert_ridgeSupport_suffix_decode_2 769 022 14 111 32 026 023 79
cert_ridgeSupport_suffix_decode_2 769 021 14 143 32 026 022 111
cert_ridgeSupport_suffix_decode_2 769 020 14 175 32 026 021 143
cert_ridgeSupport_suffix_decode_2 769 019 14 207 32 026 020 175
cert_ridgeSupport_suffix_decode_2 769 018 14 239 32 026 019 207
cert_ridgeSupport_suffix_decode_2 769 017 14 271 32 026 018 239
cert_ridgeSupport_suffix_decode_2 769 016 14 303 32 026 017 271
cert_ridgeSupport_suffix_decode_2 769 015 14 335 32 026 016 303
cert_ridgeSupport_suffix_decode_2 769 014 14 367 32 026 015 335
cert_ridgeSupport_suffix_decode_2 769 013 14 399 32 026 014 367
cert_ridgeSupport_suffix_decode_2 769 012 14 431 32 026 013 399
cert_ridgeSupport_suffix_decode_2 769 011 14 463 32 026 012 431
cert_ridgeSupport_suffix_decode_2 769 010 14 495 32 026 011 463
cert_ridgeSupport_suffix_decode_2 769 009 14 527 32 026 010 495
cert_ridgeSupport_suffix_decode_2 769 008 14 559 32 026 009 527
cert_ridgeSupport_suffix_decode_2 769 007 14 591 32 026 008 559
cert_ridgeSupport_suffix_decode_2 769 006 14 623 32 026 007 591
cert_ridgeSupport_suffix_decode_2 769 005 14 655 32 026 006 623
cert_ridgeSupport_suffix_decode_2 769 004 14 687 32 026 005 655
cert_ridgeSupport_suffix_decode_2 769 003 14 719 32 026 004 687
cert_ridgeSupport_suffix_decode_2 769 002 14 751 32 026 003 719
cert_ridgeSupport_suffix_decode_2 769 001 14 783 32 026 002 751
cert_ridgeSupport_suffix_decode_2 769 000 14 815 32 026 001 783
cert_ridgeSupport_eq_3 769
theorem ridgeTest_large_769 : ridgeTest 769 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport769_eq]
    simp only [ridgeSupport769_suffix_000, ridgeSupport769_suffix_001, ridgeSupport769_suffix_002, ridgeSupport769_suffix_003, ridgeSupport769_suffix_004, ridgeSupport769_suffix_005, ridgeSupport769_suffix_006, ridgeSupport769_suffix_007, ridgeSupport769_suffix_008, ridgeSupport769_suffix_009, ridgeSupport769_suffix_010, ridgeSupport769_suffix_011, ridgeSupport769_suffix_012, ridgeSupport769_suffix_013, ridgeSupport769_suffix_014, ridgeSupport769_suffix_015, ridgeSupport769_suffix_016, ridgeSupport769_suffix_017, ridgeSupport769_suffix_018, ridgeSupport769_suffix_019, ridgeSupport769_suffix_020, ridgeSupport769_suffix_021, ridgeSupport769_suffix_022, ridgeSupport769_suffix_023, ridgeSupport769_suffix_024, ridgeSupport769_suffix_025, ridgeSupport769_suffix_026, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport769_000_mask, ridgeSupport769_001_mask, ridgeSupport769_002_mask, ridgeSupport769_003_mask, ridgeSupport769_004_mask, ridgeSupport769_005_mask, ridgeSupport769_006_mask, ridgeSupport769_007_mask, ridgeSupport769_008_mask, ridgeSupport769_009_mask, ridgeSupport769_010_mask, ridgeSupport769_011_mask, ridgeSupport769_012_mask, ridgeSupport769_013_mask, ridgeSupport769_014_mask, ridgeSupport769_015_mask, ridgeSupport769_016_mask, ridgeSupport769_017_mask, ridgeSupport769_018_mask, ridgeSupport769_019_mask, ridgeSupport769_020_mask, ridgeSupport769_021_mask, ridgeSupport769_022_mask, ridgeSupport769_023_mask, ridgeSupport769_024_mask, ridgeSupport769_025_mask]
    decide +kernel
  · rw [ridgeSupport769_eq]
    simp only [ridgeSupport769_suffix_000, ridgeSupport769_suffix_001, ridgeSupport769_suffix_002, ridgeSupport769_suffix_003, ridgeSupport769_suffix_004, ridgeSupport769_suffix_005, ridgeSupport769_suffix_006, ridgeSupport769_suffix_007, ridgeSupport769_suffix_008, ridgeSupport769_suffix_009, ridgeSupport769_suffix_010, ridgeSupport769_suffix_011, ridgeSupport769_suffix_012, ridgeSupport769_suffix_013, ridgeSupport769_suffix_014, ridgeSupport769_suffix_015, ridgeSupport769_suffix_016, ridgeSupport769_suffix_017, ridgeSupport769_suffix_018, ridgeSupport769_suffix_019, ridgeSupport769_suffix_020, ridgeSupport769_suffix_021, ridgeSupport769_suffix_022, ridgeSupport769_suffix_023, ridgeSupport769_suffix_024, ridgeSupport769_suffix_025, ridgeSupport769_suffix_026, List.all_append, List.all_nil, ridgeSupport769_000_checked, ridgeSupport769_001_checked, ridgeSupport769_002_checked, ridgeSupport769_003_checked, ridgeSupport769_004_checked, ridgeSupport769_005_checked, ridgeSupport769_006_checked, ridgeSupport769_007_checked, ridgeSupport769_008_checked, ridgeSupport769_009_checked, ridgeSupport769_010_checked, ridgeSupport769_011_checked, ridgeSupport769_012_checked, ridgeSupport769_013_checked, ridgeSupport769_014_checked, ridgeSupport769_015_checked, ridgeSupport769_016_checked, ridgeSupport769_017_checked, ridgeSupport769_018_checked, ridgeSupport769_019_checked, ridgeSupport769_020_checked, ridgeSupport769_021_checked, ridgeSupport769_022_checked, ridgeSupport769_023_checked, ridgeSupport769_024_checked, ridgeSupport769_025_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
