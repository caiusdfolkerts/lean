module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport168Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 168 028 15
cert_ridgeSupport_suffix_decode_2 168 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 168 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 168 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 168 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 168 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 168 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 168 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 168 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 168 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 168 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 168 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 168 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 168 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 168 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 168 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 168 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 168 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 168 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 168 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 168 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 168 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 168 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 168 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 168 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 168 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 168 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 168 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 168 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 168
theorem ridgeTest_large_168 : ridgeTest 168 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport168_eq]
    simp only [ridgeSupport168_suffix_000, ridgeSupport168_suffix_001, ridgeSupport168_suffix_002, ridgeSupport168_suffix_003, ridgeSupport168_suffix_004, ridgeSupport168_suffix_005, ridgeSupport168_suffix_006, ridgeSupport168_suffix_007, ridgeSupport168_suffix_008, ridgeSupport168_suffix_009, ridgeSupport168_suffix_010, ridgeSupport168_suffix_011, ridgeSupport168_suffix_012, ridgeSupport168_suffix_013, ridgeSupport168_suffix_014, ridgeSupport168_suffix_015, ridgeSupport168_suffix_016, ridgeSupport168_suffix_017, ridgeSupport168_suffix_018, ridgeSupport168_suffix_019, ridgeSupport168_suffix_020, ridgeSupport168_suffix_021, ridgeSupport168_suffix_022, ridgeSupport168_suffix_023, ridgeSupport168_suffix_024, ridgeSupport168_suffix_025, ridgeSupport168_suffix_026, ridgeSupport168_suffix_027, ridgeSupport168_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport168_000_mask, ridgeSupport168_001_mask, ridgeSupport168_002_mask, ridgeSupport168_003_mask, ridgeSupport168_004_mask, ridgeSupport168_005_mask, ridgeSupport168_006_mask, ridgeSupport168_007_mask, ridgeSupport168_008_mask, ridgeSupport168_009_mask, ridgeSupport168_010_mask, ridgeSupport168_011_mask, ridgeSupport168_012_mask, ridgeSupport168_013_mask, ridgeSupport168_014_mask, ridgeSupport168_015_mask, ridgeSupport168_016_mask, ridgeSupport168_017_mask, ridgeSupport168_018_mask, ridgeSupport168_019_mask, ridgeSupport168_020_mask, ridgeSupport168_021_mask, ridgeSupport168_022_mask, ridgeSupport168_023_mask, ridgeSupport168_024_mask, ridgeSupport168_025_mask, ridgeSupport168_026_mask, ridgeSupport168_027_mask]
    decide +kernel
  · rw [ridgeSupport168_eq]
    simp only [ridgeSupport168_suffix_000, ridgeSupport168_suffix_001, ridgeSupport168_suffix_002, ridgeSupport168_suffix_003, ridgeSupport168_suffix_004, ridgeSupport168_suffix_005, ridgeSupport168_suffix_006, ridgeSupport168_suffix_007, ridgeSupport168_suffix_008, ridgeSupport168_suffix_009, ridgeSupport168_suffix_010, ridgeSupport168_suffix_011, ridgeSupport168_suffix_012, ridgeSupport168_suffix_013, ridgeSupport168_suffix_014, ridgeSupport168_suffix_015, ridgeSupport168_suffix_016, ridgeSupport168_suffix_017, ridgeSupport168_suffix_018, ridgeSupport168_suffix_019, ridgeSupport168_suffix_020, ridgeSupport168_suffix_021, ridgeSupport168_suffix_022, ridgeSupport168_suffix_023, ridgeSupport168_suffix_024, ridgeSupport168_suffix_025, ridgeSupport168_suffix_026, ridgeSupport168_suffix_027, ridgeSupport168_suffix_028, List.all_append, List.all_nil, ridgeSupport168_000_checked, ridgeSupport168_001_checked, ridgeSupport168_002_checked, ridgeSupport168_003_checked, ridgeSupport168_004_checked, ridgeSupport168_005_checked, ridgeSupport168_006_checked, ridgeSupport168_007_checked, ridgeSupport168_008_checked, ridgeSupport168_009_checked, ridgeSupport168_010_checked, ridgeSupport168_011_checked, ridgeSupport168_012_checked, ridgeSupport168_013_checked, ridgeSupport168_014_checked, ridgeSupport168_015_checked, ridgeSupport168_016_checked, ridgeSupport168_017_checked, ridgeSupport168_018_checked, ridgeSupport168_019_checked, ridgeSupport168_020_checked, ridgeSupport168_021_checked, ridgeSupport168_022_checked, ridgeSupport168_023_checked, ridgeSupport168_024_checked, ridgeSupport168_025_checked, ridgeSupport168_026_checked, ridgeSupport168_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
