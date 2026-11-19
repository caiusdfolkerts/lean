module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport530Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 530 028 15
cert_ridgeSupport_suffix_decode_2 530 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 530 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 530 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 530 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 530 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 530 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 530 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 530 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 530 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 530 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 530 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 530 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 530 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 530 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 530 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 530 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 530 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 530 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 530 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 530 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 530 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 530 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 530 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 530 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 530 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 530 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 530 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 530 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 530
theorem ridgeTest_large_530 : ridgeTest 530 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport530_eq]
    simp only [ridgeSupport530_suffix_000, ridgeSupport530_suffix_001, ridgeSupport530_suffix_002, ridgeSupport530_suffix_003, ridgeSupport530_suffix_004, ridgeSupport530_suffix_005, ridgeSupport530_suffix_006, ridgeSupport530_suffix_007, ridgeSupport530_suffix_008, ridgeSupport530_suffix_009, ridgeSupport530_suffix_010, ridgeSupport530_suffix_011, ridgeSupport530_suffix_012, ridgeSupport530_suffix_013, ridgeSupport530_suffix_014, ridgeSupport530_suffix_015, ridgeSupport530_suffix_016, ridgeSupport530_suffix_017, ridgeSupport530_suffix_018, ridgeSupport530_suffix_019, ridgeSupport530_suffix_020, ridgeSupport530_suffix_021, ridgeSupport530_suffix_022, ridgeSupport530_suffix_023, ridgeSupport530_suffix_024, ridgeSupport530_suffix_025, ridgeSupport530_suffix_026, ridgeSupport530_suffix_027, ridgeSupport530_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport530_000_mask, ridgeSupport530_001_mask, ridgeSupport530_002_mask, ridgeSupport530_003_mask, ridgeSupport530_004_mask, ridgeSupport530_005_mask, ridgeSupport530_006_mask, ridgeSupport530_007_mask, ridgeSupport530_008_mask, ridgeSupport530_009_mask, ridgeSupport530_010_mask, ridgeSupport530_011_mask, ridgeSupport530_012_mask, ridgeSupport530_013_mask, ridgeSupport530_014_mask, ridgeSupport530_015_mask, ridgeSupport530_016_mask, ridgeSupport530_017_mask, ridgeSupport530_018_mask, ridgeSupport530_019_mask, ridgeSupport530_020_mask, ridgeSupport530_021_mask, ridgeSupport530_022_mask, ridgeSupport530_023_mask, ridgeSupport530_024_mask, ridgeSupport530_025_mask, ridgeSupport530_026_mask, ridgeSupport530_027_mask]
    decide +kernel
  · rw [ridgeSupport530_eq]
    simp only [ridgeSupport530_suffix_000, ridgeSupport530_suffix_001, ridgeSupport530_suffix_002, ridgeSupport530_suffix_003, ridgeSupport530_suffix_004, ridgeSupport530_suffix_005, ridgeSupport530_suffix_006, ridgeSupport530_suffix_007, ridgeSupport530_suffix_008, ridgeSupport530_suffix_009, ridgeSupport530_suffix_010, ridgeSupport530_suffix_011, ridgeSupport530_suffix_012, ridgeSupport530_suffix_013, ridgeSupport530_suffix_014, ridgeSupport530_suffix_015, ridgeSupport530_suffix_016, ridgeSupport530_suffix_017, ridgeSupport530_suffix_018, ridgeSupport530_suffix_019, ridgeSupport530_suffix_020, ridgeSupport530_suffix_021, ridgeSupport530_suffix_022, ridgeSupport530_suffix_023, ridgeSupport530_suffix_024, ridgeSupport530_suffix_025, ridgeSupport530_suffix_026, ridgeSupport530_suffix_027, ridgeSupport530_suffix_028, List.all_append, List.all_nil, ridgeSupport530_000_checked, ridgeSupport530_001_checked, ridgeSupport530_002_checked, ridgeSupport530_003_checked, ridgeSupport530_004_checked, ridgeSupport530_005_checked, ridgeSupport530_006_checked, ridgeSupport530_007_checked, ridgeSupport530_008_checked, ridgeSupport530_009_checked, ridgeSupport530_010_checked, ridgeSupport530_011_checked, ridgeSupport530_012_checked, ridgeSupport530_013_checked, ridgeSupport530_014_checked, ridgeSupport530_015_checked, ridgeSupport530_016_checked, ridgeSupport530_017_checked, ridgeSupport530_018_checked, ridgeSupport530_019_checked, ridgeSupport530_020_checked, ridgeSupport530_021_checked, ridgeSupport530_022_checked, ridgeSupport530_023_checked, ridgeSupport530_024_checked, ridgeSupport530_025_checked, ridgeSupport530_026_checked, ridgeSupport530_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
