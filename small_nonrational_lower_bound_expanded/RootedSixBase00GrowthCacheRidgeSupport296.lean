module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport296Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 296 028 15
cert_ridgeSupport_suffix_decode_2 296 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 296 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 296 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 296 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 296 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 296 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 296 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 296 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 296 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 296 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 296 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 296 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 296 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 296 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 296 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 296 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 296 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 296 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 296 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 296 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 296 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 296 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 296 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 296 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 296 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 296 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 296 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 296 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 296
theorem ridgeTest_large_296 : ridgeTest 296 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport296_eq]
    simp only [ridgeSupport296_suffix_000, ridgeSupport296_suffix_001, ridgeSupport296_suffix_002, ridgeSupport296_suffix_003, ridgeSupport296_suffix_004, ridgeSupport296_suffix_005, ridgeSupport296_suffix_006, ridgeSupport296_suffix_007, ridgeSupport296_suffix_008, ridgeSupport296_suffix_009, ridgeSupport296_suffix_010, ridgeSupport296_suffix_011, ridgeSupport296_suffix_012, ridgeSupport296_suffix_013, ridgeSupport296_suffix_014, ridgeSupport296_suffix_015, ridgeSupport296_suffix_016, ridgeSupport296_suffix_017, ridgeSupport296_suffix_018, ridgeSupport296_suffix_019, ridgeSupport296_suffix_020, ridgeSupport296_suffix_021, ridgeSupport296_suffix_022, ridgeSupport296_suffix_023, ridgeSupport296_suffix_024, ridgeSupport296_suffix_025, ridgeSupport296_suffix_026, ridgeSupport296_suffix_027, ridgeSupport296_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport296_000_mask, ridgeSupport296_001_mask, ridgeSupport296_002_mask, ridgeSupport296_003_mask, ridgeSupport296_004_mask, ridgeSupport296_005_mask, ridgeSupport296_006_mask, ridgeSupport296_007_mask, ridgeSupport296_008_mask, ridgeSupport296_009_mask, ridgeSupport296_010_mask, ridgeSupport296_011_mask, ridgeSupport296_012_mask, ridgeSupport296_013_mask, ridgeSupport296_014_mask, ridgeSupport296_015_mask, ridgeSupport296_016_mask, ridgeSupport296_017_mask, ridgeSupport296_018_mask, ridgeSupport296_019_mask, ridgeSupport296_020_mask, ridgeSupport296_021_mask, ridgeSupport296_022_mask, ridgeSupport296_023_mask, ridgeSupport296_024_mask, ridgeSupport296_025_mask, ridgeSupport296_026_mask, ridgeSupport296_027_mask]
    decide +kernel
  · rw [ridgeSupport296_eq]
    simp only [ridgeSupport296_suffix_000, ridgeSupport296_suffix_001, ridgeSupport296_suffix_002, ridgeSupport296_suffix_003, ridgeSupport296_suffix_004, ridgeSupport296_suffix_005, ridgeSupport296_suffix_006, ridgeSupport296_suffix_007, ridgeSupport296_suffix_008, ridgeSupport296_suffix_009, ridgeSupport296_suffix_010, ridgeSupport296_suffix_011, ridgeSupport296_suffix_012, ridgeSupport296_suffix_013, ridgeSupport296_suffix_014, ridgeSupport296_suffix_015, ridgeSupport296_suffix_016, ridgeSupport296_suffix_017, ridgeSupport296_suffix_018, ridgeSupport296_suffix_019, ridgeSupport296_suffix_020, ridgeSupport296_suffix_021, ridgeSupport296_suffix_022, ridgeSupport296_suffix_023, ridgeSupport296_suffix_024, ridgeSupport296_suffix_025, ridgeSupport296_suffix_026, ridgeSupport296_suffix_027, ridgeSupport296_suffix_028, List.all_append, List.all_nil, ridgeSupport296_000_checked, ridgeSupport296_001_checked, ridgeSupport296_002_checked, ridgeSupport296_003_checked, ridgeSupport296_004_checked, ridgeSupport296_005_checked, ridgeSupport296_006_checked, ridgeSupport296_007_checked, ridgeSupport296_008_checked, ridgeSupport296_009_checked, ridgeSupport296_010_checked, ridgeSupport296_011_checked, ridgeSupport296_012_checked, ridgeSupport296_013_checked, ridgeSupport296_014_checked, ridgeSupport296_015_checked, ridgeSupport296_016_checked, ridgeSupport296_017_checked, ridgeSupport296_018_checked, ridgeSupport296_019_checked, ridgeSupport296_020_checked, ridgeSupport296_021_checked, ridgeSupport296_022_checked, ridgeSupport296_023_checked, ridgeSupport296_024_checked, ridgeSupport296_025_checked, ridgeSupport296_026_checked, ridgeSupport296_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
