module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport100Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 100 028 15
cert_ridgeSupport_suffix_decode_2 100 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 100 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 100 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 100 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 100 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 100 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 100 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 100 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 100 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 100 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 100 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 100 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 100 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 100 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 100 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 100 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 100 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 100 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 100 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 100 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 100 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 100 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 100 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 100 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 100 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 100 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 100 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 100 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 100
theorem ridgeTest_large_100 : ridgeTest 100 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport100_eq]
    simp only [ridgeSupport100_suffix_000, ridgeSupport100_suffix_001, ridgeSupport100_suffix_002, ridgeSupport100_suffix_003, ridgeSupport100_suffix_004, ridgeSupport100_suffix_005, ridgeSupport100_suffix_006, ridgeSupport100_suffix_007, ridgeSupport100_suffix_008, ridgeSupport100_suffix_009, ridgeSupport100_suffix_010, ridgeSupport100_suffix_011, ridgeSupport100_suffix_012, ridgeSupport100_suffix_013, ridgeSupport100_suffix_014, ridgeSupport100_suffix_015, ridgeSupport100_suffix_016, ridgeSupport100_suffix_017, ridgeSupport100_suffix_018, ridgeSupport100_suffix_019, ridgeSupport100_suffix_020, ridgeSupport100_suffix_021, ridgeSupport100_suffix_022, ridgeSupport100_suffix_023, ridgeSupport100_suffix_024, ridgeSupport100_suffix_025, ridgeSupport100_suffix_026, ridgeSupport100_suffix_027, ridgeSupport100_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport100_000_mask, ridgeSupport100_001_mask, ridgeSupport100_002_mask, ridgeSupport100_003_mask, ridgeSupport100_004_mask, ridgeSupport100_005_mask, ridgeSupport100_006_mask, ridgeSupport100_007_mask, ridgeSupport100_008_mask, ridgeSupport100_009_mask, ridgeSupport100_010_mask, ridgeSupport100_011_mask, ridgeSupport100_012_mask, ridgeSupport100_013_mask, ridgeSupport100_014_mask, ridgeSupport100_015_mask, ridgeSupport100_016_mask, ridgeSupport100_017_mask, ridgeSupport100_018_mask, ridgeSupport100_019_mask, ridgeSupport100_020_mask, ridgeSupport100_021_mask, ridgeSupport100_022_mask, ridgeSupport100_023_mask, ridgeSupport100_024_mask, ridgeSupport100_025_mask, ridgeSupport100_026_mask, ridgeSupport100_027_mask]
    decide +kernel
  · rw [ridgeSupport100_eq]
    simp only [ridgeSupport100_suffix_000, ridgeSupport100_suffix_001, ridgeSupport100_suffix_002, ridgeSupport100_suffix_003, ridgeSupport100_suffix_004, ridgeSupport100_suffix_005, ridgeSupport100_suffix_006, ridgeSupport100_suffix_007, ridgeSupport100_suffix_008, ridgeSupport100_suffix_009, ridgeSupport100_suffix_010, ridgeSupport100_suffix_011, ridgeSupport100_suffix_012, ridgeSupport100_suffix_013, ridgeSupport100_suffix_014, ridgeSupport100_suffix_015, ridgeSupport100_suffix_016, ridgeSupport100_suffix_017, ridgeSupport100_suffix_018, ridgeSupport100_suffix_019, ridgeSupport100_suffix_020, ridgeSupport100_suffix_021, ridgeSupport100_suffix_022, ridgeSupport100_suffix_023, ridgeSupport100_suffix_024, ridgeSupport100_suffix_025, ridgeSupport100_suffix_026, ridgeSupport100_suffix_027, ridgeSupport100_suffix_028, List.all_append, List.all_nil, ridgeSupport100_000_checked, ridgeSupport100_001_checked, ridgeSupport100_002_checked, ridgeSupport100_003_checked, ridgeSupport100_004_checked, ridgeSupport100_005_checked, ridgeSupport100_006_checked, ridgeSupport100_007_checked, ridgeSupport100_008_checked, ridgeSupport100_009_checked, ridgeSupport100_010_checked, ridgeSupport100_011_checked, ridgeSupport100_012_checked, ridgeSupport100_013_checked, ridgeSupport100_014_checked, ridgeSupport100_015_checked, ridgeSupport100_016_checked, ridgeSupport100_017_checked, ridgeSupport100_018_checked, ridgeSupport100_019_checked, ridgeSupport100_020_checked, ridgeSupport100_021_checked, ridgeSupport100_022_checked, ridgeSupport100_023_checked, ridgeSupport100_024_checked, ridgeSupport100_025_checked, ridgeSupport100_026_checked, ridgeSupport100_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
