module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport176Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 176 028 15
cert_ridgeSupport_suffix_decode_2 176 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 176 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 176 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 176 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 176 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 176 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 176 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 176 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 176 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 176 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 176 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 176 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 176 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 176 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 176 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 176 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 176 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 176 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 176 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 176 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 176 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 176 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 176 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 176 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 176 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 176 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 176 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 176 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 176
theorem ridgeTest_large_176 : ridgeTest 176 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport176_eq]
    simp only [ridgeSupport176_suffix_000, ridgeSupport176_suffix_001, ridgeSupport176_suffix_002, ridgeSupport176_suffix_003, ridgeSupport176_suffix_004, ridgeSupport176_suffix_005, ridgeSupport176_suffix_006, ridgeSupport176_suffix_007, ridgeSupport176_suffix_008, ridgeSupport176_suffix_009, ridgeSupport176_suffix_010, ridgeSupport176_suffix_011, ridgeSupport176_suffix_012, ridgeSupport176_suffix_013, ridgeSupport176_suffix_014, ridgeSupport176_suffix_015, ridgeSupport176_suffix_016, ridgeSupport176_suffix_017, ridgeSupport176_suffix_018, ridgeSupport176_suffix_019, ridgeSupport176_suffix_020, ridgeSupport176_suffix_021, ridgeSupport176_suffix_022, ridgeSupport176_suffix_023, ridgeSupport176_suffix_024, ridgeSupport176_suffix_025, ridgeSupport176_suffix_026, ridgeSupport176_suffix_027, ridgeSupport176_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport176_000_mask, ridgeSupport176_001_mask, ridgeSupport176_002_mask, ridgeSupport176_003_mask, ridgeSupport176_004_mask, ridgeSupport176_005_mask, ridgeSupport176_006_mask, ridgeSupport176_007_mask, ridgeSupport176_008_mask, ridgeSupport176_009_mask, ridgeSupport176_010_mask, ridgeSupport176_011_mask, ridgeSupport176_012_mask, ridgeSupport176_013_mask, ridgeSupport176_014_mask, ridgeSupport176_015_mask, ridgeSupport176_016_mask, ridgeSupport176_017_mask, ridgeSupport176_018_mask, ridgeSupport176_019_mask, ridgeSupport176_020_mask, ridgeSupport176_021_mask, ridgeSupport176_022_mask, ridgeSupport176_023_mask, ridgeSupport176_024_mask, ridgeSupport176_025_mask, ridgeSupport176_026_mask, ridgeSupport176_027_mask]
    decide +kernel
  · rw [ridgeSupport176_eq]
    simp only [ridgeSupport176_suffix_000, ridgeSupport176_suffix_001, ridgeSupport176_suffix_002, ridgeSupport176_suffix_003, ridgeSupport176_suffix_004, ridgeSupport176_suffix_005, ridgeSupport176_suffix_006, ridgeSupport176_suffix_007, ridgeSupport176_suffix_008, ridgeSupport176_suffix_009, ridgeSupport176_suffix_010, ridgeSupport176_suffix_011, ridgeSupport176_suffix_012, ridgeSupport176_suffix_013, ridgeSupport176_suffix_014, ridgeSupport176_suffix_015, ridgeSupport176_suffix_016, ridgeSupport176_suffix_017, ridgeSupport176_suffix_018, ridgeSupport176_suffix_019, ridgeSupport176_suffix_020, ridgeSupport176_suffix_021, ridgeSupport176_suffix_022, ridgeSupport176_suffix_023, ridgeSupport176_suffix_024, ridgeSupport176_suffix_025, ridgeSupport176_suffix_026, ridgeSupport176_suffix_027, ridgeSupport176_suffix_028, List.all_append, List.all_nil, ridgeSupport176_000_checked, ridgeSupport176_001_checked, ridgeSupport176_002_checked, ridgeSupport176_003_checked, ridgeSupport176_004_checked, ridgeSupport176_005_checked, ridgeSupport176_006_checked, ridgeSupport176_007_checked, ridgeSupport176_008_checked, ridgeSupport176_009_checked, ridgeSupport176_010_checked, ridgeSupport176_011_checked, ridgeSupport176_012_checked, ridgeSupport176_013_checked, ridgeSupport176_014_checked, ridgeSupport176_015_checked, ridgeSupport176_016_checked, ridgeSupport176_017_checked, ridgeSupport176_018_checked, ridgeSupport176_019_checked, ridgeSupport176_020_checked, ridgeSupport176_021_checked, ridgeSupport176_022_checked, ridgeSupport176_023_checked, ridgeSupport176_024_checked, ridgeSupport176_025_checked, ridgeSupport176_026_checked, ridgeSupport176_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
