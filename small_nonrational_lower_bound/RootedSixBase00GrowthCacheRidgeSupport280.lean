module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport280Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 280 028 15
cert_ridgeSupport_suffix_decode_2 280 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 280 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 280 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 280 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 280 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 280 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 280 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 280 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 280 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 280 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 280 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 280 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 280 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 280 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 280 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 280 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 280 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 280 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 280 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 280 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 280 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 280 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 280 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 280 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 280 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 280 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 280 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 280 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 280
theorem ridgeTest_large_280 : ridgeTest 280 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport280_eq]
    simp only [ridgeSupport280_suffix_000, ridgeSupport280_suffix_001, ridgeSupport280_suffix_002, ridgeSupport280_suffix_003, ridgeSupport280_suffix_004, ridgeSupport280_suffix_005, ridgeSupport280_suffix_006, ridgeSupport280_suffix_007, ridgeSupport280_suffix_008, ridgeSupport280_suffix_009, ridgeSupport280_suffix_010, ridgeSupport280_suffix_011, ridgeSupport280_suffix_012, ridgeSupport280_suffix_013, ridgeSupport280_suffix_014, ridgeSupport280_suffix_015, ridgeSupport280_suffix_016, ridgeSupport280_suffix_017, ridgeSupport280_suffix_018, ridgeSupport280_suffix_019, ridgeSupport280_suffix_020, ridgeSupport280_suffix_021, ridgeSupport280_suffix_022, ridgeSupport280_suffix_023, ridgeSupport280_suffix_024, ridgeSupport280_suffix_025, ridgeSupport280_suffix_026, ridgeSupport280_suffix_027, ridgeSupport280_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport280_000_mask, ridgeSupport280_001_mask, ridgeSupport280_002_mask, ridgeSupport280_003_mask, ridgeSupport280_004_mask, ridgeSupport280_005_mask, ridgeSupport280_006_mask, ridgeSupport280_007_mask, ridgeSupport280_008_mask, ridgeSupport280_009_mask, ridgeSupport280_010_mask, ridgeSupport280_011_mask, ridgeSupport280_012_mask, ridgeSupport280_013_mask, ridgeSupport280_014_mask, ridgeSupport280_015_mask, ridgeSupport280_016_mask, ridgeSupport280_017_mask, ridgeSupport280_018_mask, ridgeSupport280_019_mask, ridgeSupport280_020_mask, ridgeSupport280_021_mask, ridgeSupport280_022_mask, ridgeSupport280_023_mask, ridgeSupport280_024_mask, ridgeSupport280_025_mask, ridgeSupport280_026_mask, ridgeSupport280_027_mask]
    decide +kernel
  · rw [ridgeSupport280_eq]
    simp only [ridgeSupport280_suffix_000, ridgeSupport280_suffix_001, ridgeSupport280_suffix_002, ridgeSupport280_suffix_003, ridgeSupport280_suffix_004, ridgeSupport280_suffix_005, ridgeSupport280_suffix_006, ridgeSupport280_suffix_007, ridgeSupport280_suffix_008, ridgeSupport280_suffix_009, ridgeSupport280_suffix_010, ridgeSupport280_suffix_011, ridgeSupport280_suffix_012, ridgeSupport280_suffix_013, ridgeSupport280_suffix_014, ridgeSupport280_suffix_015, ridgeSupport280_suffix_016, ridgeSupport280_suffix_017, ridgeSupport280_suffix_018, ridgeSupport280_suffix_019, ridgeSupport280_suffix_020, ridgeSupport280_suffix_021, ridgeSupport280_suffix_022, ridgeSupport280_suffix_023, ridgeSupport280_suffix_024, ridgeSupport280_suffix_025, ridgeSupport280_suffix_026, ridgeSupport280_suffix_027, ridgeSupport280_suffix_028, List.all_append, List.all_nil, ridgeSupport280_000_checked, ridgeSupport280_001_checked, ridgeSupport280_002_checked, ridgeSupport280_003_checked, ridgeSupport280_004_checked, ridgeSupport280_005_checked, ridgeSupport280_006_checked, ridgeSupport280_007_checked, ridgeSupport280_008_checked, ridgeSupport280_009_checked, ridgeSupport280_010_checked, ridgeSupport280_011_checked, ridgeSupport280_012_checked, ridgeSupport280_013_checked, ridgeSupport280_014_checked, ridgeSupport280_015_checked, ridgeSupport280_016_checked, ridgeSupport280_017_checked, ridgeSupport280_018_checked, ridgeSupport280_019_checked, ridgeSupport280_020_checked, ridgeSupport280_021_checked, ridgeSupport280_022_checked, ridgeSupport280_023_checked, ridgeSupport280_024_checked, ridgeSupport280_025_checked, ridgeSupport280_026_checked, ridgeSupport280_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
