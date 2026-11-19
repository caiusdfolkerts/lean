module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport641Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 641 026 14
cert_ridgeSupport_suffix_decode_2 641 025 14 15 15 026 026 0
cert_ridgeSupport_suffix_decode_2 641 024 14 47 32 026 025 15
cert_ridgeSupport_suffix_decode_2 641 023 14 79 32 026 024 47
cert_ridgeSupport_suffix_decode_2 641 022 14 111 32 026 023 79
cert_ridgeSupport_suffix_decode_2 641 021 14 143 32 026 022 111
cert_ridgeSupport_suffix_decode_2 641 020 14 175 32 026 021 143
cert_ridgeSupport_suffix_decode_2 641 019 14 207 32 026 020 175
cert_ridgeSupport_suffix_decode_2 641 018 14 239 32 026 019 207
cert_ridgeSupport_suffix_decode_2 641 017 14 271 32 026 018 239
cert_ridgeSupport_suffix_decode_2 641 016 14 303 32 026 017 271
cert_ridgeSupport_suffix_decode_2 641 015 14 335 32 026 016 303
cert_ridgeSupport_suffix_decode_2 641 014 14 367 32 026 015 335
cert_ridgeSupport_suffix_decode_2 641 013 14 399 32 026 014 367
cert_ridgeSupport_suffix_decode_2 641 012 14 431 32 026 013 399
cert_ridgeSupport_suffix_decode_2 641 011 14 463 32 026 012 431
cert_ridgeSupport_suffix_decode_2 641 010 14 495 32 026 011 463
cert_ridgeSupport_suffix_decode_2 641 009 14 527 32 026 010 495
cert_ridgeSupport_suffix_decode_2 641 008 14 559 32 026 009 527
cert_ridgeSupport_suffix_decode_2 641 007 14 591 32 026 008 559
cert_ridgeSupport_suffix_decode_2 641 006 14 623 32 026 007 591
cert_ridgeSupport_suffix_decode_2 641 005 14 655 32 026 006 623
cert_ridgeSupport_suffix_decode_2 641 004 14 687 32 026 005 655
cert_ridgeSupport_suffix_decode_2 641 003 14 719 32 026 004 687
cert_ridgeSupport_suffix_decode_2 641 002 14 751 32 026 003 719
cert_ridgeSupport_suffix_decode_2 641 001 14 783 32 026 002 751
cert_ridgeSupport_suffix_decode_2 641 000 14 815 32 026 001 783
cert_ridgeSupport_eq_3 641
theorem ridgeTest_large_641 : ridgeTest 641 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport641_eq]
    simp only [ridgeSupport641_suffix_000, ridgeSupport641_suffix_001, ridgeSupport641_suffix_002, ridgeSupport641_suffix_003, ridgeSupport641_suffix_004, ridgeSupport641_suffix_005, ridgeSupport641_suffix_006, ridgeSupport641_suffix_007, ridgeSupport641_suffix_008, ridgeSupport641_suffix_009, ridgeSupport641_suffix_010, ridgeSupport641_suffix_011, ridgeSupport641_suffix_012, ridgeSupport641_suffix_013, ridgeSupport641_suffix_014, ridgeSupport641_suffix_015, ridgeSupport641_suffix_016, ridgeSupport641_suffix_017, ridgeSupport641_suffix_018, ridgeSupport641_suffix_019, ridgeSupport641_suffix_020, ridgeSupport641_suffix_021, ridgeSupport641_suffix_022, ridgeSupport641_suffix_023, ridgeSupport641_suffix_024, ridgeSupport641_suffix_025, ridgeSupport641_suffix_026, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport641_000_mask, ridgeSupport641_001_mask, ridgeSupport641_002_mask, ridgeSupport641_003_mask, ridgeSupport641_004_mask, ridgeSupport641_005_mask, ridgeSupport641_006_mask, ridgeSupport641_007_mask, ridgeSupport641_008_mask, ridgeSupport641_009_mask, ridgeSupport641_010_mask, ridgeSupport641_011_mask, ridgeSupport641_012_mask, ridgeSupport641_013_mask, ridgeSupport641_014_mask, ridgeSupport641_015_mask, ridgeSupport641_016_mask, ridgeSupport641_017_mask, ridgeSupport641_018_mask, ridgeSupport641_019_mask, ridgeSupport641_020_mask, ridgeSupport641_021_mask, ridgeSupport641_022_mask, ridgeSupport641_023_mask, ridgeSupport641_024_mask, ridgeSupport641_025_mask]
    decide +kernel
  · rw [ridgeSupport641_eq]
    simp only [ridgeSupport641_suffix_000, ridgeSupport641_suffix_001, ridgeSupport641_suffix_002, ridgeSupport641_suffix_003, ridgeSupport641_suffix_004, ridgeSupport641_suffix_005, ridgeSupport641_suffix_006, ridgeSupport641_suffix_007, ridgeSupport641_suffix_008, ridgeSupport641_suffix_009, ridgeSupport641_suffix_010, ridgeSupport641_suffix_011, ridgeSupport641_suffix_012, ridgeSupport641_suffix_013, ridgeSupport641_suffix_014, ridgeSupport641_suffix_015, ridgeSupport641_suffix_016, ridgeSupport641_suffix_017, ridgeSupport641_suffix_018, ridgeSupport641_suffix_019, ridgeSupport641_suffix_020, ridgeSupport641_suffix_021, ridgeSupport641_suffix_022, ridgeSupport641_suffix_023, ridgeSupport641_suffix_024, ridgeSupport641_suffix_025, ridgeSupport641_suffix_026, List.all_append, List.all_nil, ridgeSupport641_000_checked, ridgeSupport641_001_checked, ridgeSupport641_002_checked, ridgeSupport641_003_checked, ridgeSupport641_004_checked, ridgeSupport641_005_checked, ridgeSupport641_006_checked, ridgeSupport641_007_checked, ridgeSupport641_008_checked, ridgeSupport641_009_checked, ridgeSupport641_010_checked, ridgeSupport641_011_checked, ridgeSupport641_012_checked, ridgeSupport641_013_checked, ridgeSupport641_014_checked, ridgeSupport641_015_checked, ridgeSupport641_016_checked, ridgeSupport641_017_checked, ridgeSupport641_018_checked, ridgeSupport641_019_checked, ridgeSupport641_020_checked, ridgeSupport641_021_checked, ridgeSupport641_022_checked, ridgeSupport641_023_checked, ridgeSupport641_024_checked, ridgeSupport641_025_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
