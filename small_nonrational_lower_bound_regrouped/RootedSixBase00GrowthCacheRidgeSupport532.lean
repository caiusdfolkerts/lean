module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport532Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 532 028 15
cert_ridgeSupport_suffix_decode_2 532 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 532 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 532 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 532 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 532 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 532 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 532 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 532 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 532 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 532 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 532 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 532 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 532 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 532 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 532 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 532 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 532 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 532 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 532 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 532 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 532 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 532 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 532 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 532 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 532 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 532 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 532 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 532 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 532
theorem ridgeTest_large_532 : ridgeTest 532 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport532_eq]
    simp only [ridgeSupport532_suffix_000, ridgeSupport532_suffix_001, ridgeSupport532_suffix_002, ridgeSupport532_suffix_003, ridgeSupport532_suffix_004, ridgeSupport532_suffix_005, ridgeSupport532_suffix_006, ridgeSupport532_suffix_007, ridgeSupport532_suffix_008, ridgeSupport532_suffix_009, ridgeSupport532_suffix_010, ridgeSupport532_suffix_011, ridgeSupport532_suffix_012, ridgeSupport532_suffix_013, ridgeSupport532_suffix_014, ridgeSupport532_suffix_015, ridgeSupport532_suffix_016, ridgeSupport532_suffix_017, ridgeSupport532_suffix_018, ridgeSupport532_suffix_019, ridgeSupport532_suffix_020, ridgeSupport532_suffix_021, ridgeSupport532_suffix_022, ridgeSupport532_suffix_023, ridgeSupport532_suffix_024, ridgeSupport532_suffix_025, ridgeSupport532_suffix_026, ridgeSupport532_suffix_027, ridgeSupport532_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport532_000_mask, ridgeSupport532_001_mask, ridgeSupport532_002_mask, ridgeSupport532_003_mask, ridgeSupport532_004_mask, ridgeSupport532_005_mask, ridgeSupport532_006_mask, ridgeSupport532_007_mask, ridgeSupport532_008_mask, ridgeSupport532_009_mask, ridgeSupport532_010_mask, ridgeSupport532_011_mask, ridgeSupport532_012_mask, ridgeSupport532_013_mask, ridgeSupport532_014_mask, ridgeSupport532_015_mask, ridgeSupport532_016_mask, ridgeSupport532_017_mask, ridgeSupport532_018_mask, ridgeSupport532_019_mask, ridgeSupport532_020_mask, ridgeSupport532_021_mask, ridgeSupport532_022_mask, ridgeSupport532_023_mask, ridgeSupport532_024_mask, ridgeSupport532_025_mask, ridgeSupport532_026_mask, ridgeSupport532_027_mask]
    decide +kernel
  · rw [ridgeSupport532_eq]
    simp only [ridgeSupport532_suffix_000, ridgeSupport532_suffix_001, ridgeSupport532_suffix_002, ridgeSupport532_suffix_003, ridgeSupport532_suffix_004, ridgeSupport532_suffix_005, ridgeSupport532_suffix_006, ridgeSupport532_suffix_007, ridgeSupport532_suffix_008, ridgeSupport532_suffix_009, ridgeSupport532_suffix_010, ridgeSupport532_suffix_011, ridgeSupport532_suffix_012, ridgeSupport532_suffix_013, ridgeSupport532_suffix_014, ridgeSupport532_suffix_015, ridgeSupport532_suffix_016, ridgeSupport532_suffix_017, ridgeSupport532_suffix_018, ridgeSupport532_suffix_019, ridgeSupport532_suffix_020, ridgeSupport532_suffix_021, ridgeSupport532_suffix_022, ridgeSupport532_suffix_023, ridgeSupport532_suffix_024, ridgeSupport532_suffix_025, ridgeSupport532_suffix_026, ridgeSupport532_suffix_027, ridgeSupport532_suffix_028, List.all_append, List.all_nil, ridgeSupport532_000_checked, ridgeSupport532_001_checked, ridgeSupport532_002_checked, ridgeSupport532_003_checked, ridgeSupport532_004_checked, ridgeSupport532_005_checked, ridgeSupport532_006_checked, ridgeSupport532_007_checked, ridgeSupport532_008_checked, ridgeSupport532_009_checked, ridgeSupport532_010_checked, ridgeSupport532_011_checked, ridgeSupport532_012_checked, ridgeSupport532_013_checked, ridgeSupport532_014_checked, ridgeSupport532_015_checked, ridgeSupport532_016_checked, ridgeSupport532_017_checked, ridgeSupport532_018_checked, ridgeSupport532_019_checked, ridgeSupport532_020_checked, ridgeSupport532_021_checked, ridgeSupport532_022_checked, ridgeSupport532_023_checked, ridgeSupport532_024_checked, ridgeSupport532_025_checked, ridgeSupport532_026_checked, ridgeSupport532_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
