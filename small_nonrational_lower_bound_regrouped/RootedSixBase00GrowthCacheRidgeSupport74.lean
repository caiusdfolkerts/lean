module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport74Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 74 028 15
cert_ridgeSupport_suffix_decode_2 74 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 74 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 74 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 74 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 74 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 74 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 74 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 74 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 74 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 74 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 74 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 74 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 74 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 74 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 74 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 74 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 74 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 74 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 74 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 74 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 74 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 74 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 74 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 74 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 74 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 74 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 74 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 74 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 74
theorem ridgeTest_large_74 : ridgeTest 74 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport74_eq]
    simp only [ridgeSupport74_suffix_000, ridgeSupport74_suffix_001, ridgeSupport74_suffix_002, ridgeSupport74_suffix_003, ridgeSupport74_suffix_004, ridgeSupport74_suffix_005, ridgeSupport74_suffix_006, ridgeSupport74_suffix_007, ridgeSupport74_suffix_008, ridgeSupport74_suffix_009, ridgeSupport74_suffix_010, ridgeSupport74_suffix_011, ridgeSupport74_suffix_012, ridgeSupport74_suffix_013, ridgeSupport74_suffix_014, ridgeSupport74_suffix_015, ridgeSupport74_suffix_016, ridgeSupport74_suffix_017, ridgeSupport74_suffix_018, ridgeSupport74_suffix_019, ridgeSupport74_suffix_020, ridgeSupport74_suffix_021, ridgeSupport74_suffix_022, ridgeSupport74_suffix_023, ridgeSupport74_suffix_024, ridgeSupport74_suffix_025, ridgeSupport74_suffix_026, ridgeSupport74_suffix_027, ridgeSupport74_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport74_000_mask, ridgeSupport74_001_mask, ridgeSupport74_002_mask, ridgeSupport74_003_mask, ridgeSupport74_004_mask, ridgeSupport74_005_mask, ridgeSupport74_006_mask, ridgeSupport74_007_mask, ridgeSupport74_008_mask, ridgeSupport74_009_mask, ridgeSupport74_010_mask, ridgeSupport74_011_mask, ridgeSupport74_012_mask, ridgeSupport74_013_mask, ridgeSupport74_014_mask, ridgeSupport74_015_mask, ridgeSupport74_016_mask, ridgeSupport74_017_mask, ridgeSupport74_018_mask, ridgeSupport74_019_mask, ridgeSupport74_020_mask, ridgeSupport74_021_mask, ridgeSupport74_022_mask, ridgeSupport74_023_mask, ridgeSupport74_024_mask, ridgeSupport74_025_mask, ridgeSupport74_026_mask, ridgeSupport74_027_mask]
    decide +kernel
  · rw [ridgeSupport74_eq]
    simp only [ridgeSupport74_suffix_000, ridgeSupport74_suffix_001, ridgeSupport74_suffix_002, ridgeSupport74_suffix_003, ridgeSupport74_suffix_004, ridgeSupport74_suffix_005, ridgeSupport74_suffix_006, ridgeSupport74_suffix_007, ridgeSupport74_suffix_008, ridgeSupport74_suffix_009, ridgeSupport74_suffix_010, ridgeSupport74_suffix_011, ridgeSupport74_suffix_012, ridgeSupport74_suffix_013, ridgeSupport74_suffix_014, ridgeSupport74_suffix_015, ridgeSupport74_suffix_016, ridgeSupport74_suffix_017, ridgeSupport74_suffix_018, ridgeSupport74_suffix_019, ridgeSupport74_suffix_020, ridgeSupport74_suffix_021, ridgeSupport74_suffix_022, ridgeSupport74_suffix_023, ridgeSupport74_suffix_024, ridgeSupport74_suffix_025, ridgeSupport74_suffix_026, ridgeSupport74_suffix_027, ridgeSupport74_suffix_028, List.all_append, List.all_nil, ridgeSupport74_000_checked, ridgeSupport74_001_checked, ridgeSupport74_002_checked, ridgeSupport74_003_checked, ridgeSupport74_004_checked, ridgeSupport74_005_checked, ridgeSupport74_006_checked, ridgeSupport74_007_checked, ridgeSupport74_008_checked, ridgeSupport74_009_checked, ridgeSupport74_010_checked, ridgeSupport74_011_checked, ridgeSupport74_012_checked, ridgeSupport74_013_checked, ridgeSupport74_014_checked, ridgeSupport74_015_checked, ridgeSupport74_016_checked, ridgeSupport74_017_checked, ridgeSupport74_018_checked, ridgeSupport74_019_checked, ridgeSupport74_020_checked, ridgeSupport74_021_checked, ridgeSupport74_022_checked, ridgeSupport74_023_checked, ridgeSupport74_024_checked, ridgeSupport74_025_checked, ridgeSupport74_026_checked, ridgeSupport74_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
