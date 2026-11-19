module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport276Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 276 028 15
cert_ridgeSupport_suffix_decode_2 276 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 276 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 276 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 276 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 276 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 276 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 276 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 276 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 276 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 276 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 276 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 276 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 276 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 276 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 276 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 276 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 276 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 276 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 276 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 276 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 276 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 276 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 276 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 276 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 276 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 276 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 276 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 276 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 276
theorem ridgeTest_large_276 : ridgeTest 276 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport276_eq]
    simp only [ridgeSupport276_suffix_000, ridgeSupport276_suffix_001, ridgeSupport276_suffix_002, ridgeSupport276_suffix_003, ridgeSupport276_suffix_004, ridgeSupport276_suffix_005, ridgeSupport276_suffix_006, ridgeSupport276_suffix_007, ridgeSupport276_suffix_008, ridgeSupport276_suffix_009, ridgeSupport276_suffix_010, ridgeSupport276_suffix_011, ridgeSupport276_suffix_012, ridgeSupport276_suffix_013, ridgeSupport276_suffix_014, ridgeSupport276_suffix_015, ridgeSupport276_suffix_016, ridgeSupport276_suffix_017, ridgeSupport276_suffix_018, ridgeSupport276_suffix_019, ridgeSupport276_suffix_020, ridgeSupport276_suffix_021, ridgeSupport276_suffix_022, ridgeSupport276_suffix_023, ridgeSupport276_suffix_024, ridgeSupport276_suffix_025, ridgeSupport276_suffix_026, ridgeSupport276_suffix_027, ridgeSupport276_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport276_000_mask, ridgeSupport276_001_mask, ridgeSupport276_002_mask, ridgeSupport276_003_mask, ridgeSupport276_004_mask, ridgeSupport276_005_mask, ridgeSupport276_006_mask, ridgeSupport276_007_mask, ridgeSupport276_008_mask, ridgeSupport276_009_mask, ridgeSupport276_010_mask, ridgeSupport276_011_mask, ridgeSupport276_012_mask, ridgeSupport276_013_mask, ridgeSupport276_014_mask, ridgeSupport276_015_mask, ridgeSupport276_016_mask, ridgeSupport276_017_mask, ridgeSupport276_018_mask, ridgeSupport276_019_mask, ridgeSupport276_020_mask, ridgeSupport276_021_mask, ridgeSupport276_022_mask, ridgeSupport276_023_mask, ridgeSupport276_024_mask, ridgeSupport276_025_mask, ridgeSupport276_026_mask, ridgeSupport276_027_mask]
    decide +kernel
  · rw [ridgeSupport276_eq]
    simp only [ridgeSupport276_suffix_000, ridgeSupport276_suffix_001, ridgeSupport276_suffix_002, ridgeSupport276_suffix_003, ridgeSupport276_suffix_004, ridgeSupport276_suffix_005, ridgeSupport276_suffix_006, ridgeSupport276_suffix_007, ridgeSupport276_suffix_008, ridgeSupport276_suffix_009, ridgeSupport276_suffix_010, ridgeSupport276_suffix_011, ridgeSupport276_suffix_012, ridgeSupport276_suffix_013, ridgeSupport276_suffix_014, ridgeSupport276_suffix_015, ridgeSupport276_suffix_016, ridgeSupport276_suffix_017, ridgeSupport276_suffix_018, ridgeSupport276_suffix_019, ridgeSupport276_suffix_020, ridgeSupport276_suffix_021, ridgeSupport276_suffix_022, ridgeSupport276_suffix_023, ridgeSupport276_suffix_024, ridgeSupport276_suffix_025, ridgeSupport276_suffix_026, ridgeSupport276_suffix_027, ridgeSupport276_suffix_028, List.all_append, List.all_nil, ridgeSupport276_000_checked, ridgeSupport276_001_checked, ridgeSupport276_002_checked, ridgeSupport276_003_checked, ridgeSupport276_004_checked, ridgeSupport276_005_checked, ridgeSupport276_006_checked, ridgeSupport276_007_checked, ridgeSupport276_008_checked, ridgeSupport276_009_checked, ridgeSupport276_010_checked, ridgeSupport276_011_checked, ridgeSupport276_012_checked, ridgeSupport276_013_checked, ridgeSupport276_014_checked, ridgeSupport276_015_checked, ridgeSupport276_016_checked, ridgeSupport276_017_checked, ridgeSupport276_018_checked, ridgeSupport276_019_checked, ridgeSupport276_020_checked, ridgeSupport276_021_checked, ridgeSupport276_022_checked, ridgeSupport276_023_checked, ridgeSupport276_024_checked, ridgeSupport276_025_checked, ridgeSupport276_026_checked, ridgeSupport276_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
