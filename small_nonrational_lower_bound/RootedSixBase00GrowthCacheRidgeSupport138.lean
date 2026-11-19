module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport138Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 138 028 15
cert_ridgeSupport_suffix_decode_2 138 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 138 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 138 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 138 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 138 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 138 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 138 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 138 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 138 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 138 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 138 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 138 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 138 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 138 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 138 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 138 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 138 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 138 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 138 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 138 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 138 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 138 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 138 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 138 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 138 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 138 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 138 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 138 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 138
theorem ridgeTest_large_138 : ridgeTest 138 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport138_eq]
    simp only [ridgeSupport138_suffix_000, ridgeSupport138_suffix_001, ridgeSupport138_suffix_002, ridgeSupport138_suffix_003, ridgeSupport138_suffix_004, ridgeSupport138_suffix_005, ridgeSupport138_suffix_006, ridgeSupport138_suffix_007, ridgeSupport138_suffix_008, ridgeSupport138_suffix_009, ridgeSupport138_suffix_010, ridgeSupport138_suffix_011, ridgeSupport138_suffix_012, ridgeSupport138_suffix_013, ridgeSupport138_suffix_014, ridgeSupport138_suffix_015, ridgeSupport138_suffix_016, ridgeSupport138_suffix_017, ridgeSupport138_suffix_018, ridgeSupport138_suffix_019, ridgeSupport138_suffix_020, ridgeSupport138_suffix_021, ridgeSupport138_suffix_022, ridgeSupport138_suffix_023, ridgeSupport138_suffix_024, ridgeSupport138_suffix_025, ridgeSupport138_suffix_026, ridgeSupport138_suffix_027, ridgeSupport138_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport138_000_mask, ridgeSupport138_001_mask, ridgeSupport138_002_mask, ridgeSupport138_003_mask, ridgeSupport138_004_mask, ridgeSupport138_005_mask, ridgeSupport138_006_mask, ridgeSupport138_007_mask, ridgeSupport138_008_mask, ridgeSupport138_009_mask, ridgeSupport138_010_mask, ridgeSupport138_011_mask, ridgeSupport138_012_mask, ridgeSupport138_013_mask, ridgeSupport138_014_mask, ridgeSupport138_015_mask, ridgeSupport138_016_mask, ridgeSupport138_017_mask, ridgeSupport138_018_mask, ridgeSupport138_019_mask, ridgeSupport138_020_mask, ridgeSupport138_021_mask, ridgeSupport138_022_mask, ridgeSupport138_023_mask, ridgeSupport138_024_mask, ridgeSupport138_025_mask, ridgeSupport138_026_mask, ridgeSupport138_027_mask]
    decide +kernel
  · rw [ridgeSupport138_eq]
    simp only [ridgeSupport138_suffix_000, ridgeSupport138_suffix_001, ridgeSupport138_suffix_002, ridgeSupport138_suffix_003, ridgeSupport138_suffix_004, ridgeSupport138_suffix_005, ridgeSupport138_suffix_006, ridgeSupport138_suffix_007, ridgeSupport138_suffix_008, ridgeSupport138_suffix_009, ridgeSupport138_suffix_010, ridgeSupport138_suffix_011, ridgeSupport138_suffix_012, ridgeSupport138_suffix_013, ridgeSupport138_suffix_014, ridgeSupport138_suffix_015, ridgeSupport138_suffix_016, ridgeSupport138_suffix_017, ridgeSupport138_suffix_018, ridgeSupport138_suffix_019, ridgeSupport138_suffix_020, ridgeSupport138_suffix_021, ridgeSupport138_suffix_022, ridgeSupport138_suffix_023, ridgeSupport138_suffix_024, ridgeSupport138_suffix_025, ridgeSupport138_suffix_026, ridgeSupport138_suffix_027, ridgeSupport138_suffix_028, List.all_append, List.all_nil, ridgeSupport138_000_checked, ridgeSupport138_001_checked, ridgeSupport138_002_checked, ridgeSupport138_003_checked, ridgeSupport138_004_checked, ridgeSupport138_005_checked, ridgeSupport138_006_checked, ridgeSupport138_007_checked, ridgeSupport138_008_checked, ridgeSupport138_009_checked, ridgeSupport138_010_checked, ridgeSupport138_011_checked, ridgeSupport138_012_checked, ridgeSupport138_013_checked, ridgeSupport138_014_checked, ridgeSupport138_015_checked, ridgeSupport138_016_checked, ridgeSupport138_017_checked, ridgeSupport138_018_checked, ridgeSupport138_019_checked, ridgeSupport138_020_checked, ridgeSupport138_021_checked, ridgeSupport138_022_checked, ridgeSupport138_023_checked, ridgeSupport138_024_checked, ridgeSupport138_025_checked, ridgeSupport138_026_checked, ridgeSupport138_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
