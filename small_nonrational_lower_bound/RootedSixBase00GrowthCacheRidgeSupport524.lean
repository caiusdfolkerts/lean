module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport524Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 524 028 15
cert_ridgeSupport_suffix_decode_2 524 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 524 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 524 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 524 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 524 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 524 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 524 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 524 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 524 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 524 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 524 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 524 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 524 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 524 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 524 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 524 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 524 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 524 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 524 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 524 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 524 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 524 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 524 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 524 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 524 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 524 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 524 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 524 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 524
theorem ridgeTest_large_524 : ridgeTest 524 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport524_eq]
    simp only [ridgeSupport524_suffix_000, ridgeSupport524_suffix_001, ridgeSupport524_suffix_002, ridgeSupport524_suffix_003, ridgeSupport524_suffix_004, ridgeSupport524_suffix_005, ridgeSupport524_suffix_006, ridgeSupport524_suffix_007, ridgeSupport524_suffix_008, ridgeSupport524_suffix_009, ridgeSupport524_suffix_010, ridgeSupport524_suffix_011, ridgeSupport524_suffix_012, ridgeSupport524_suffix_013, ridgeSupport524_suffix_014, ridgeSupport524_suffix_015, ridgeSupport524_suffix_016, ridgeSupport524_suffix_017, ridgeSupport524_suffix_018, ridgeSupport524_suffix_019, ridgeSupport524_suffix_020, ridgeSupport524_suffix_021, ridgeSupport524_suffix_022, ridgeSupport524_suffix_023, ridgeSupport524_suffix_024, ridgeSupport524_suffix_025, ridgeSupport524_suffix_026, ridgeSupport524_suffix_027, ridgeSupport524_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport524_000_mask, ridgeSupport524_001_mask, ridgeSupport524_002_mask, ridgeSupport524_003_mask, ridgeSupport524_004_mask, ridgeSupport524_005_mask, ridgeSupport524_006_mask, ridgeSupport524_007_mask, ridgeSupport524_008_mask, ridgeSupport524_009_mask, ridgeSupport524_010_mask, ridgeSupport524_011_mask, ridgeSupport524_012_mask, ridgeSupport524_013_mask, ridgeSupport524_014_mask, ridgeSupport524_015_mask, ridgeSupport524_016_mask, ridgeSupport524_017_mask, ridgeSupport524_018_mask, ridgeSupport524_019_mask, ridgeSupport524_020_mask, ridgeSupport524_021_mask, ridgeSupport524_022_mask, ridgeSupport524_023_mask, ridgeSupport524_024_mask, ridgeSupport524_025_mask, ridgeSupport524_026_mask, ridgeSupport524_027_mask]
    decide +kernel
  · rw [ridgeSupport524_eq]
    simp only [ridgeSupport524_suffix_000, ridgeSupport524_suffix_001, ridgeSupport524_suffix_002, ridgeSupport524_suffix_003, ridgeSupport524_suffix_004, ridgeSupport524_suffix_005, ridgeSupport524_suffix_006, ridgeSupport524_suffix_007, ridgeSupport524_suffix_008, ridgeSupport524_suffix_009, ridgeSupport524_suffix_010, ridgeSupport524_suffix_011, ridgeSupport524_suffix_012, ridgeSupport524_suffix_013, ridgeSupport524_suffix_014, ridgeSupport524_suffix_015, ridgeSupport524_suffix_016, ridgeSupport524_suffix_017, ridgeSupport524_suffix_018, ridgeSupport524_suffix_019, ridgeSupport524_suffix_020, ridgeSupport524_suffix_021, ridgeSupport524_suffix_022, ridgeSupport524_suffix_023, ridgeSupport524_suffix_024, ridgeSupport524_suffix_025, ridgeSupport524_suffix_026, ridgeSupport524_suffix_027, ridgeSupport524_suffix_028, List.all_append, List.all_nil, ridgeSupport524_000_checked, ridgeSupport524_001_checked, ridgeSupport524_002_checked, ridgeSupport524_003_checked, ridgeSupport524_004_checked, ridgeSupport524_005_checked, ridgeSupport524_006_checked, ridgeSupport524_007_checked, ridgeSupport524_008_checked, ridgeSupport524_009_checked, ridgeSupport524_010_checked, ridgeSupport524_011_checked, ridgeSupport524_012_checked, ridgeSupport524_013_checked, ridgeSupport524_014_checked, ridgeSupport524_015_checked, ridgeSupport524_016_checked, ridgeSupport524_017_checked, ridgeSupport524_018_checked, ridgeSupport524_019_checked, ridgeSupport524_020_checked, ridgeSupport524_021_checked, ridgeSupport524_022_checked, ridgeSupport524_023_checked, ridgeSupport524_024_checked, ridgeSupport524_025_checked, ridgeSupport524_026_checked, ridgeSupport524_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
