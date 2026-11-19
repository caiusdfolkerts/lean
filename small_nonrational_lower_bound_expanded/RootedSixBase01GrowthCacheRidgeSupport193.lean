module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport193Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 193 026 14
cert_ridgeSupport_suffix_decode_2 193 025 14 15 15 026 026 0
cert_ridgeSupport_suffix_decode_2 193 024 14 47 32 026 025 15
cert_ridgeSupport_suffix_decode_2 193 023 14 79 32 026 024 47
cert_ridgeSupport_suffix_decode_2 193 022 14 111 32 026 023 79
cert_ridgeSupport_suffix_decode_2 193 021 14 143 32 026 022 111
cert_ridgeSupport_suffix_decode_2 193 020 14 175 32 026 021 143
cert_ridgeSupport_suffix_decode_2 193 019 14 207 32 026 020 175
cert_ridgeSupport_suffix_decode_2 193 018 14 239 32 026 019 207
cert_ridgeSupport_suffix_decode_2 193 017 14 271 32 026 018 239
cert_ridgeSupport_suffix_decode_2 193 016 14 303 32 026 017 271
cert_ridgeSupport_suffix_decode_2 193 015 14 335 32 026 016 303
cert_ridgeSupport_suffix_decode_2 193 014 14 367 32 026 015 335
cert_ridgeSupport_suffix_decode_2 193 013 14 399 32 026 014 367
cert_ridgeSupport_suffix_decode_2 193 012 14 431 32 026 013 399
cert_ridgeSupport_suffix_decode_2 193 011 14 463 32 026 012 431
cert_ridgeSupport_suffix_decode_2 193 010 14 495 32 026 011 463
cert_ridgeSupport_suffix_decode_2 193 009 14 527 32 026 010 495
cert_ridgeSupport_suffix_decode_2 193 008 14 559 32 026 009 527
cert_ridgeSupport_suffix_decode_2 193 007 14 591 32 026 008 559
cert_ridgeSupport_suffix_decode_2 193 006 14 623 32 026 007 591
cert_ridgeSupport_suffix_decode_2 193 005 14 655 32 026 006 623
cert_ridgeSupport_suffix_decode_2 193 004 14 687 32 026 005 655
cert_ridgeSupport_suffix_decode_2 193 003 14 719 32 026 004 687
cert_ridgeSupport_suffix_decode_2 193 002 14 751 32 026 003 719
cert_ridgeSupport_suffix_decode_2 193 001 14 783 32 026 002 751
cert_ridgeSupport_suffix_decode_2 193 000 14 815 32 026 001 783
cert_ridgeSupport_eq_3 193
theorem ridgeTest_large_193 : ridgeTest 193 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport193_eq]
    simp only [ridgeSupport193_suffix_000, ridgeSupport193_suffix_001, ridgeSupport193_suffix_002, ridgeSupport193_suffix_003, ridgeSupport193_suffix_004, ridgeSupport193_suffix_005, ridgeSupport193_suffix_006, ridgeSupport193_suffix_007, ridgeSupport193_suffix_008, ridgeSupport193_suffix_009, ridgeSupport193_suffix_010, ridgeSupport193_suffix_011, ridgeSupport193_suffix_012, ridgeSupport193_suffix_013, ridgeSupport193_suffix_014, ridgeSupport193_suffix_015, ridgeSupport193_suffix_016, ridgeSupport193_suffix_017, ridgeSupport193_suffix_018, ridgeSupport193_suffix_019, ridgeSupport193_suffix_020, ridgeSupport193_suffix_021, ridgeSupport193_suffix_022, ridgeSupport193_suffix_023, ridgeSupport193_suffix_024, ridgeSupport193_suffix_025, ridgeSupport193_suffix_026, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport193_000_mask, ridgeSupport193_001_mask, ridgeSupport193_002_mask, ridgeSupport193_003_mask, ridgeSupport193_004_mask, ridgeSupport193_005_mask, ridgeSupport193_006_mask, ridgeSupport193_007_mask, ridgeSupport193_008_mask, ridgeSupport193_009_mask, ridgeSupport193_010_mask, ridgeSupport193_011_mask, ridgeSupport193_012_mask, ridgeSupport193_013_mask, ridgeSupport193_014_mask, ridgeSupport193_015_mask, ridgeSupport193_016_mask, ridgeSupport193_017_mask, ridgeSupport193_018_mask, ridgeSupport193_019_mask, ridgeSupport193_020_mask, ridgeSupport193_021_mask, ridgeSupport193_022_mask, ridgeSupport193_023_mask, ridgeSupport193_024_mask, ridgeSupport193_025_mask]
    decide +kernel
  · rw [ridgeSupport193_eq]
    simp only [ridgeSupport193_suffix_000, ridgeSupport193_suffix_001, ridgeSupport193_suffix_002, ridgeSupport193_suffix_003, ridgeSupport193_suffix_004, ridgeSupport193_suffix_005, ridgeSupport193_suffix_006, ridgeSupport193_suffix_007, ridgeSupport193_suffix_008, ridgeSupport193_suffix_009, ridgeSupport193_suffix_010, ridgeSupport193_suffix_011, ridgeSupport193_suffix_012, ridgeSupport193_suffix_013, ridgeSupport193_suffix_014, ridgeSupport193_suffix_015, ridgeSupport193_suffix_016, ridgeSupport193_suffix_017, ridgeSupport193_suffix_018, ridgeSupport193_suffix_019, ridgeSupport193_suffix_020, ridgeSupport193_suffix_021, ridgeSupport193_suffix_022, ridgeSupport193_suffix_023, ridgeSupport193_suffix_024, ridgeSupport193_suffix_025, ridgeSupport193_suffix_026, List.all_append, List.all_nil, ridgeSupport193_000_checked, ridgeSupport193_001_checked, ridgeSupport193_002_checked, ridgeSupport193_003_checked, ridgeSupport193_004_checked, ridgeSupport193_005_checked, ridgeSupport193_006_checked, ridgeSupport193_007_checked, ridgeSupport193_008_checked, ridgeSupport193_009_checked, ridgeSupport193_010_checked, ridgeSupport193_011_checked, ridgeSupport193_012_checked, ridgeSupport193_013_checked, ridgeSupport193_014_checked, ridgeSupport193_015_checked, ridgeSupport193_016_checked, ridgeSupport193_017_checked, ridgeSupport193_018_checked, ridgeSupport193_019_checked, ridgeSupport193_020_checked, ridgeSupport193_021_checked, ridgeSupport193_022_checked, ridgeSupport193_023_checked, ridgeSupport193_024_checked, ridgeSupport193_025_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
