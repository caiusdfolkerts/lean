module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport385Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 385 026 14
cert_ridgeSupport_suffix_decode_2 385 025 14 15 15 026 026 0
cert_ridgeSupport_suffix_decode_2 385 024 14 47 32 026 025 15
cert_ridgeSupport_suffix_decode_2 385 023 14 79 32 026 024 47
cert_ridgeSupport_suffix_decode_2 385 022 14 111 32 026 023 79
cert_ridgeSupport_suffix_decode_2 385 021 14 143 32 026 022 111
cert_ridgeSupport_suffix_decode_2 385 020 14 175 32 026 021 143
cert_ridgeSupport_suffix_decode_2 385 019 14 207 32 026 020 175
cert_ridgeSupport_suffix_decode_2 385 018 14 239 32 026 019 207
cert_ridgeSupport_suffix_decode_2 385 017 14 271 32 026 018 239
cert_ridgeSupport_suffix_decode_2 385 016 14 303 32 026 017 271
cert_ridgeSupport_suffix_decode_2 385 015 14 335 32 026 016 303
cert_ridgeSupport_suffix_decode_2 385 014 14 367 32 026 015 335
cert_ridgeSupport_suffix_decode_2 385 013 14 399 32 026 014 367
cert_ridgeSupport_suffix_decode_2 385 012 14 431 32 026 013 399
cert_ridgeSupport_suffix_decode_2 385 011 14 463 32 026 012 431
cert_ridgeSupport_suffix_decode_2 385 010 14 495 32 026 011 463
cert_ridgeSupport_suffix_decode_2 385 009 14 527 32 026 010 495
cert_ridgeSupport_suffix_decode_2 385 008 14 559 32 026 009 527
cert_ridgeSupport_suffix_decode_2 385 007 14 591 32 026 008 559
cert_ridgeSupport_suffix_decode_2 385 006 14 623 32 026 007 591
cert_ridgeSupport_suffix_decode_2 385 005 14 655 32 026 006 623
cert_ridgeSupport_suffix_decode_2 385 004 14 687 32 026 005 655
cert_ridgeSupport_suffix_decode_2 385 003 14 719 32 026 004 687
cert_ridgeSupport_suffix_decode_2 385 002 14 751 32 026 003 719
cert_ridgeSupport_suffix_decode_2 385 001 14 783 32 026 002 751
cert_ridgeSupport_suffix_decode_2 385 000 14 815 32 026 001 783
cert_ridgeSupport_eq_3 385
theorem ridgeTest_large_385 : ridgeTest 385 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport385_eq]
    simp only [ridgeSupport385_suffix_000, ridgeSupport385_suffix_001, ridgeSupport385_suffix_002, ridgeSupport385_suffix_003, ridgeSupport385_suffix_004, ridgeSupport385_suffix_005, ridgeSupport385_suffix_006, ridgeSupport385_suffix_007, ridgeSupport385_suffix_008, ridgeSupport385_suffix_009, ridgeSupport385_suffix_010, ridgeSupport385_suffix_011, ridgeSupport385_suffix_012, ridgeSupport385_suffix_013, ridgeSupport385_suffix_014, ridgeSupport385_suffix_015, ridgeSupport385_suffix_016, ridgeSupport385_suffix_017, ridgeSupport385_suffix_018, ridgeSupport385_suffix_019, ridgeSupport385_suffix_020, ridgeSupport385_suffix_021, ridgeSupport385_suffix_022, ridgeSupport385_suffix_023, ridgeSupport385_suffix_024, ridgeSupport385_suffix_025, ridgeSupport385_suffix_026, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport385_000_mask, ridgeSupport385_001_mask, ridgeSupport385_002_mask, ridgeSupport385_003_mask, ridgeSupport385_004_mask, ridgeSupport385_005_mask, ridgeSupport385_006_mask, ridgeSupport385_007_mask, ridgeSupport385_008_mask, ridgeSupport385_009_mask, ridgeSupport385_010_mask, ridgeSupport385_011_mask, ridgeSupport385_012_mask, ridgeSupport385_013_mask, ridgeSupport385_014_mask, ridgeSupport385_015_mask, ridgeSupport385_016_mask, ridgeSupport385_017_mask, ridgeSupport385_018_mask, ridgeSupport385_019_mask, ridgeSupport385_020_mask, ridgeSupport385_021_mask, ridgeSupport385_022_mask, ridgeSupport385_023_mask, ridgeSupport385_024_mask, ridgeSupport385_025_mask]
    decide +kernel
  · rw [ridgeSupport385_eq]
    simp only [ridgeSupport385_suffix_000, ridgeSupport385_suffix_001, ridgeSupport385_suffix_002, ridgeSupport385_suffix_003, ridgeSupport385_suffix_004, ridgeSupport385_suffix_005, ridgeSupport385_suffix_006, ridgeSupport385_suffix_007, ridgeSupport385_suffix_008, ridgeSupport385_suffix_009, ridgeSupport385_suffix_010, ridgeSupport385_suffix_011, ridgeSupport385_suffix_012, ridgeSupport385_suffix_013, ridgeSupport385_suffix_014, ridgeSupport385_suffix_015, ridgeSupport385_suffix_016, ridgeSupport385_suffix_017, ridgeSupport385_suffix_018, ridgeSupport385_suffix_019, ridgeSupport385_suffix_020, ridgeSupport385_suffix_021, ridgeSupport385_suffix_022, ridgeSupport385_suffix_023, ridgeSupport385_suffix_024, ridgeSupport385_suffix_025, ridgeSupport385_suffix_026, List.all_append, List.all_nil, ridgeSupport385_000_checked, ridgeSupport385_001_checked, ridgeSupport385_002_checked, ridgeSupport385_003_checked, ridgeSupport385_004_checked, ridgeSupport385_005_checked, ridgeSupport385_006_checked, ridgeSupport385_007_checked, ridgeSupport385_008_checked, ridgeSupport385_009_checked, ridgeSupport385_010_checked, ridgeSupport385_011_checked, ridgeSupport385_012_checked, ridgeSupport385_013_checked, ridgeSupport385_014_checked, ridgeSupport385_015_checked, ridgeSupport385_016_checked, ridgeSupport385_017_checked, ridgeSupport385_018_checked, ridgeSupport385_019_checked, ridgeSupport385_020_checked, ridgeSupport385_021_checked, ridgeSupport385_022_checked, ridgeSupport385_023_checked, ridgeSupport385_024_checked, ridgeSupport385_025_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
