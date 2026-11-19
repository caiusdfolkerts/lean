module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport261Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 261 028 15
cert_ridgeSupport_suffix_decode_2 261 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 261 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 261 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 261 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 261 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 261 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 261 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 261 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 261 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 261 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 261 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 261 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 261 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 261 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 261 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 261 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 261 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 261 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 261 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 261 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 261 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 261 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 261 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 261 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 261 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 261 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 261 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 261 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 261
theorem ridgeTest_large_261 : ridgeTest 261 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport261_eq]
    simp only [ridgeSupport261_suffix_000, ridgeSupport261_suffix_001, ridgeSupport261_suffix_002, ridgeSupport261_suffix_003, ridgeSupport261_suffix_004, ridgeSupport261_suffix_005, ridgeSupport261_suffix_006, ridgeSupport261_suffix_007, ridgeSupport261_suffix_008, ridgeSupport261_suffix_009, ridgeSupport261_suffix_010, ridgeSupport261_suffix_011, ridgeSupport261_suffix_012, ridgeSupport261_suffix_013, ridgeSupport261_suffix_014, ridgeSupport261_suffix_015, ridgeSupport261_suffix_016, ridgeSupport261_suffix_017, ridgeSupport261_suffix_018, ridgeSupport261_suffix_019, ridgeSupport261_suffix_020, ridgeSupport261_suffix_021, ridgeSupport261_suffix_022, ridgeSupport261_suffix_023, ridgeSupport261_suffix_024, ridgeSupport261_suffix_025, ridgeSupport261_suffix_026, ridgeSupport261_suffix_027, ridgeSupport261_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport261_000_mask, ridgeSupport261_001_mask, ridgeSupport261_002_mask, ridgeSupport261_003_mask, ridgeSupport261_004_mask, ridgeSupport261_005_mask, ridgeSupport261_006_mask, ridgeSupport261_007_mask, ridgeSupport261_008_mask, ridgeSupport261_009_mask, ridgeSupport261_010_mask, ridgeSupport261_011_mask, ridgeSupport261_012_mask, ridgeSupport261_013_mask, ridgeSupport261_014_mask, ridgeSupport261_015_mask, ridgeSupport261_016_mask, ridgeSupport261_017_mask, ridgeSupport261_018_mask, ridgeSupport261_019_mask, ridgeSupport261_020_mask, ridgeSupport261_021_mask, ridgeSupport261_022_mask, ridgeSupport261_023_mask, ridgeSupport261_024_mask, ridgeSupport261_025_mask, ridgeSupport261_026_mask, ridgeSupport261_027_mask]
    decide +kernel
  · rw [ridgeSupport261_eq]
    simp only [ridgeSupport261_suffix_000, ridgeSupport261_suffix_001, ridgeSupport261_suffix_002, ridgeSupport261_suffix_003, ridgeSupport261_suffix_004, ridgeSupport261_suffix_005, ridgeSupport261_suffix_006, ridgeSupport261_suffix_007, ridgeSupport261_suffix_008, ridgeSupport261_suffix_009, ridgeSupport261_suffix_010, ridgeSupport261_suffix_011, ridgeSupport261_suffix_012, ridgeSupport261_suffix_013, ridgeSupport261_suffix_014, ridgeSupport261_suffix_015, ridgeSupport261_suffix_016, ridgeSupport261_suffix_017, ridgeSupport261_suffix_018, ridgeSupport261_suffix_019, ridgeSupport261_suffix_020, ridgeSupport261_suffix_021, ridgeSupport261_suffix_022, ridgeSupport261_suffix_023, ridgeSupport261_suffix_024, ridgeSupport261_suffix_025, ridgeSupport261_suffix_026, ridgeSupport261_suffix_027, ridgeSupport261_suffix_028, List.all_append, List.all_nil, ridgeSupport261_000_checked, ridgeSupport261_001_checked, ridgeSupport261_002_checked, ridgeSupport261_003_checked, ridgeSupport261_004_checked, ridgeSupport261_005_checked, ridgeSupport261_006_checked, ridgeSupport261_007_checked, ridgeSupport261_008_checked, ridgeSupport261_009_checked, ridgeSupport261_010_checked, ridgeSupport261_011_checked, ridgeSupport261_012_checked, ridgeSupport261_013_checked, ridgeSupport261_014_checked, ridgeSupport261_015_checked, ridgeSupport261_016_checked, ridgeSupport261_017_checked, ridgeSupport261_018_checked, ridgeSupport261_019_checked, ridgeSupport261_020_checked, ridgeSupport261_021_checked, ridgeSupport261_022_checked, ridgeSupport261_023_checked, ridgeSupport261_024_checked, ridgeSupport261_025_checked, ridgeSupport261_026_checked, ridgeSupport261_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
