module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport76Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 76 028 15
cert_ridgeSupport_suffix_decode_2 76 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 76 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 76 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 76 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 76 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 76 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 76 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 76 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 76 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 76 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 76 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 76 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 76 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 76 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 76 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 76 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 76 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 76 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 76 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 76 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 76 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 76 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 76 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 76 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 76 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 76 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 76 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 76 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 76
theorem ridgeTest_large_76 : ridgeTest 76 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport76_eq]
    simp only [ridgeSupport76_suffix_000, ridgeSupport76_suffix_001, ridgeSupport76_suffix_002, ridgeSupport76_suffix_003, ridgeSupport76_suffix_004, ridgeSupport76_suffix_005, ridgeSupport76_suffix_006, ridgeSupport76_suffix_007, ridgeSupport76_suffix_008, ridgeSupport76_suffix_009, ridgeSupport76_suffix_010, ridgeSupport76_suffix_011, ridgeSupport76_suffix_012, ridgeSupport76_suffix_013, ridgeSupport76_suffix_014, ridgeSupport76_suffix_015, ridgeSupport76_suffix_016, ridgeSupport76_suffix_017, ridgeSupport76_suffix_018, ridgeSupport76_suffix_019, ridgeSupport76_suffix_020, ridgeSupport76_suffix_021, ridgeSupport76_suffix_022, ridgeSupport76_suffix_023, ridgeSupport76_suffix_024, ridgeSupport76_suffix_025, ridgeSupport76_suffix_026, ridgeSupport76_suffix_027, ridgeSupport76_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport76_000_mask, ridgeSupport76_001_mask, ridgeSupport76_002_mask, ridgeSupport76_003_mask, ridgeSupport76_004_mask, ridgeSupport76_005_mask, ridgeSupport76_006_mask, ridgeSupport76_007_mask, ridgeSupport76_008_mask, ridgeSupport76_009_mask, ridgeSupport76_010_mask, ridgeSupport76_011_mask, ridgeSupport76_012_mask, ridgeSupport76_013_mask, ridgeSupport76_014_mask, ridgeSupport76_015_mask, ridgeSupport76_016_mask, ridgeSupport76_017_mask, ridgeSupport76_018_mask, ridgeSupport76_019_mask, ridgeSupport76_020_mask, ridgeSupport76_021_mask, ridgeSupport76_022_mask, ridgeSupport76_023_mask, ridgeSupport76_024_mask, ridgeSupport76_025_mask, ridgeSupport76_026_mask, ridgeSupport76_027_mask]
    decide +kernel
  · rw [ridgeSupport76_eq]
    simp only [ridgeSupport76_suffix_000, ridgeSupport76_suffix_001, ridgeSupport76_suffix_002, ridgeSupport76_suffix_003, ridgeSupport76_suffix_004, ridgeSupport76_suffix_005, ridgeSupport76_suffix_006, ridgeSupport76_suffix_007, ridgeSupport76_suffix_008, ridgeSupport76_suffix_009, ridgeSupport76_suffix_010, ridgeSupport76_suffix_011, ridgeSupport76_suffix_012, ridgeSupport76_suffix_013, ridgeSupport76_suffix_014, ridgeSupport76_suffix_015, ridgeSupport76_suffix_016, ridgeSupport76_suffix_017, ridgeSupport76_suffix_018, ridgeSupport76_suffix_019, ridgeSupport76_suffix_020, ridgeSupport76_suffix_021, ridgeSupport76_suffix_022, ridgeSupport76_suffix_023, ridgeSupport76_suffix_024, ridgeSupport76_suffix_025, ridgeSupport76_suffix_026, ridgeSupport76_suffix_027, ridgeSupport76_suffix_028, List.all_append, List.all_nil, ridgeSupport76_000_checked, ridgeSupport76_001_checked, ridgeSupport76_002_checked, ridgeSupport76_003_checked, ridgeSupport76_004_checked, ridgeSupport76_005_checked, ridgeSupport76_006_checked, ridgeSupport76_007_checked, ridgeSupport76_008_checked, ridgeSupport76_009_checked, ridgeSupport76_010_checked, ridgeSupport76_011_checked, ridgeSupport76_012_checked, ridgeSupport76_013_checked, ridgeSupport76_014_checked, ridgeSupport76_015_checked, ridgeSupport76_016_checked, ridgeSupport76_017_checked, ridgeSupport76_018_checked, ridgeSupport76_019_checked, ridgeSupport76_020_checked, ridgeSupport76_021_checked, ridgeSupport76_022_checked, ridgeSupport76_023_checked, ridgeSupport76_024_checked, ridgeSupport76_025_checked, ridgeSupport76_026_checked, ridgeSupport76_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
