module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport577Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 577 026 14
cert_ridgeSupport_suffix_decode_2 577 025 14 15 15 026 026 0
cert_ridgeSupport_suffix_decode_2 577 024 14 47 32 026 025 15
cert_ridgeSupport_suffix_decode_2 577 023 14 79 32 026 024 47
cert_ridgeSupport_suffix_decode_2 577 022 14 111 32 026 023 79
cert_ridgeSupport_suffix_decode_2 577 021 14 143 32 026 022 111
cert_ridgeSupport_suffix_decode_2 577 020 14 175 32 026 021 143
cert_ridgeSupport_suffix_decode_2 577 019 14 207 32 026 020 175
cert_ridgeSupport_suffix_decode_2 577 018 14 239 32 026 019 207
cert_ridgeSupport_suffix_decode_2 577 017 14 271 32 026 018 239
cert_ridgeSupport_suffix_decode_2 577 016 14 303 32 026 017 271
cert_ridgeSupport_suffix_decode_2 577 015 14 335 32 026 016 303
cert_ridgeSupport_suffix_decode_2 577 014 14 367 32 026 015 335
cert_ridgeSupport_suffix_decode_2 577 013 14 399 32 026 014 367
cert_ridgeSupport_suffix_decode_2 577 012 14 431 32 026 013 399
cert_ridgeSupport_suffix_decode_2 577 011 14 463 32 026 012 431
cert_ridgeSupport_suffix_decode_2 577 010 14 495 32 026 011 463
cert_ridgeSupport_suffix_decode_2 577 009 14 527 32 026 010 495
cert_ridgeSupport_suffix_decode_2 577 008 14 559 32 026 009 527
cert_ridgeSupport_suffix_decode_2 577 007 14 591 32 026 008 559
cert_ridgeSupport_suffix_decode_2 577 006 14 623 32 026 007 591
cert_ridgeSupport_suffix_decode_2 577 005 14 655 32 026 006 623
cert_ridgeSupport_suffix_decode_2 577 004 14 687 32 026 005 655
cert_ridgeSupport_suffix_decode_2 577 003 14 719 32 026 004 687
cert_ridgeSupport_suffix_decode_2 577 002 14 751 32 026 003 719
cert_ridgeSupport_suffix_decode_2 577 001 14 783 32 026 002 751
cert_ridgeSupport_suffix_decode_2 577 000 14 815 32 026 001 783
cert_ridgeSupport_eq_3 577
theorem ridgeTest_large_577 : ridgeTest 577 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport577_eq]
    simp only [ridgeSupport577_suffix_000, ridgeSupport577_suffix_001, ridgeSupport577_suffix_002, ridgeSupport577_suffix_003, ridgeSupport577_suffix_004, ridgeSupport577_suffix_005, ridgeSupport577_suffix_006, ridgeSupport577_suffix_007, ridgeSupport577_suffix_008, ridgeSupport577_suffix_009, ridgeSupport577_suffix_010, ridgeSupport577_suffix_011, ridgeSupport577_suffix_012, ridgeSupport577_suffix_013, ridgeSupport577_suffix_014, ridgeSupport577_suffix_015, ridgeSupport577_suffix_016, ridgeSupport577_suffix_017, ridgeSupport577_suffix_018, ridgeSupport577_suffix_019, ridgeSupport577_suffix_020, ridgeSupport577_suffix_021, ridgeSupport577_suffix_022, ridgeSupport577_suffix_023, ridgeSupport577_suffix_024, ridgeSupport577_suffix_025, ridgeSupport577_suffix_026, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport577_000_mask, ridgeSupport577_001_mask, ridgeSupport577_002_mask, ridgeSupport577_003_mask, ridgeSupport577_004_mask, ridgeSupport577_005_mask, ridgeSupport577_006_mask, ridgeSupport577_007_mask, ridgeSupport577_008_mask, ridgeSupport577_009_mask, ridgeSupport577_010_mask, ridgeSupport577_011_mask, ridgeSupport577_012_mask, ridgeSupport577_013_mask, ridgeSupport577_014_mask, ridgeSupport577_015_mask, ridgeSupport577_016_mask, ridgeSupport577_017_mask, ridgeSupport577_018_mask, ridgeSupport577_019_mask, ridgeSupport577_020_mask, ridgeSupport577_021_mask, ridgeSupport577_022_mask, ridgeSupport577_023_mask, ridgeSupport577_024_mask, ridgeSupport577_025_mask]
    decide +kernel
  · rw [ridgeSupport577_eq]
    simp only [ridgeSupport577_suffix_000, ridgeSupport577_suffix_001, ridgeSupport577_suffix_002, ridgeSupport577_suffix_003, ridgeSupport577_suffix_004, ridgeSupport577_suffix_005, ridgeSupport577_suffix_006, ridgeSupport577_suffix_007, ridgeSupport577_suffix_008, ridgeSupport577_suffix_009, ridgeSupport577_suffix_010, ridgeSupport577_suffix_011, ridgeSupport577_suffix_012, ridgeSupport577_suffix_013, ridgeSupport577_suffix_014, ridgeSupport577_suffix_015, ridgeSupport577_suffix_016, ridgeSupport577_suffix_017, ridgeSupport577_suffix_018, ridgeSupport577_suffix_019, ridgeSupport577_suffix_020, ridgeSupport577_suffix_021, ridgeSupport577_suffix_022, ridgeSupport577_suffix_023, ridgeSupport577_suffix_024, ridgeSupport577_suffix_025, ridgeSupport577_suffix_026, List.all_append, List.all_nil, ridgeSupport577_000_checked, ridgeSupport577_001_checked, ridgeSupport577_002_checked, ridgeSupport577_003_checked, ridgeSupport577_004_checked, ridgeSupport577_005_checked, ridgeSupport577_006_checked, ridgeSupport577_007_checked, ridgeSupport577_008_checked, ridgeSupport577_009_checked, ridgeSupport577_010_checked, ridgeSupport577_011_checked, ridgeSupport577_012_checked, ridgeSupport577_013_checked, ridgeSupport577_014_checked, ridgeSupport577_015_checked, ridgeSupport577_016_checked, ridgeSupport577_017_checked, ridgeSupport577_018_checked, ridgeSupport577_019_checked, ridgeSupport577_020_checked, ridgeSupport577_021_checked, ridgeSupport577_022_checked, ridgeSupport577_023_checked, ridgeSupport577_024_checked, ridgeSupport577_025_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
