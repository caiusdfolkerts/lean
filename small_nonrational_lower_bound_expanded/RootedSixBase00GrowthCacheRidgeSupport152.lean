module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport152Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 152 028 15
cert_ridgeSupport_suffix_decode_2 152 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 152 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 152 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 152 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 152 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 152 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 152 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 152 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 152 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 152 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 152 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 152 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 152 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 152 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 152 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 152 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 152 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 152 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 152 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 152 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 152 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 152 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 152 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 152 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 152 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 152 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 152 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 152 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 152
theorem ridgeTest_large_152 : ridgeTest 152 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport152_eq]
    simp only [ridgeSupport152_suffix_000, ridgeSupport152_suffix_001, ridgeSupport152_suffix_002, ridgeSupport152_suffix_003, ridgeSupport152_suffix_004, ridgeSupport152_suffix_005, ridgeSupport152_suffix_006, ridgeSupport152_suffix_007, ridgeSupport152_suffix_008, ridgeSupport152_suffix_009, ridgeSupport152_suffix_010, ridgeSupport152_suffix_011, ridgeSupport152_suffix_012, ridgeSupport152_suffix_013, ridgeSupport152_suffix_014, ridgeSupport152_suffix_015, ridgeSupport152_suffix_016, ridgeSupport152_suffix_017, ridgeSupport152_suffix_018, ridgeSupport152_suffix_019, ridgeSupport152_suffix_020, ridgeSupport152_suffix_021, ridgeSupport152_suffix_022, ridgeSupport152_suffix_023, ridgeSupport152_suffix_024, ridgeSupport152_suffix_025, ridgeSupport152_suffix_026, ridgeSupport152_suffix_027, ridgeSupport152_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport152_000_mask, ridgeSupport152_001_mask, ridgeSupport152_002_mask, ridgeSupport152_003_mask, ridgeSupport152_004_mask, ridgeSupport152_005_mask, ridgeSupport152_006_mask, ridgeSupport152_007_mask, ridgeSupport152_008_mask, ridgeSupport152_009_mask, ridgeSupport152_010_mask, ridgeSupport152_011_mask, ridgeSupport152_012_mask, ridgeSupport152_013_mask, ridgeSupport152_014_mask, ridgeSupport152_015_mask, ridgeSupport152_016_mask, ridgeSupport152_017_mask, ridgeSupport152_018_mask, ridgeSupport152_019_mask, ridgeSupport152_020_mask, ridgeSupport152_021_mask, ridgeSupport152_022_mask, ridgeSupport152_023_mask, ridgeSupport152_024_mask, ridgeSupport152_025_mask, ridgeSupport152_026_mask, ridgeSupport152_027_mask]
    decide +kernel
  · rw [ridgeSupport152_eq]
    simp only [ridgeSupport152_suffix_000, ridgeSupport152_suffix_001, ridgeSupport152_suffix_002, ridgeSupport152_suffix_003, ridgeSupport152_suffix_004, ridgeSupport152_suffix_005, ridgeSupport152_suffix_006, ridgeSupport152_suffix_007, ridgeSupport152_suffix_008, ridgeSupport152_suffix_009, ridgeSupport152_suffix_010, ridgeSupport152_suffix_011, ridgeSupport152_suffix_012, ridgeSupport152_suffix_013, ridgeSupport152_suffix_014, ridgeSupport152_suffix_015, ridgeSupport152_suffix_016, ridgeSupport152_suffix_017, ridgeSupport152_suffix_018, ridgeSupport152_suffix_019, ridgeSupport152_suffix_020, ridgeSupport152_suffix_021, ridgeSupport152_suffix_022, ridgeSupport152_suffix_023, ridgeSupport152_suffix_024, ridgeSupport152_suffix_025, ridgeSupport152_suffix_026, ridgeSupport152_suffix_027, ridgeSupport152_suffix_028, List.all_append, List.all_nil, ridgeSupport152_000_checked, ridgeSupport152_001_checked, ridgeSupport152_002_checked, ridgeSupport152_003_checked, ridgeSupport152_004_checked, ridgeSupport152_005_checked, ridgeSupport152_006_checked, ridgeSupport152_007_checked, ridgeSupport152_008_checked, ridgeSupport152_009_checked, ridgeSupport152_010_checked, ridgeSupport152_011_checked, ridgeSupport152_012_checked, ridgeSupport152_013_checked, ridgeSupport152_014_checked, ridgeSupport152_015_checked, ridgeSupport152_016_checked, ridgeSupport152_017_checked, ridgeSupport152_018_checked, ridgeSupport152_019_checked, ridgeSupport152_020_checked, ridgeSupport152_021_checked, ridgeSupport152_022_checked, ridgeSupport152_023_checked, ridgeSupport152_024_checked, ridgeSupport152_025_checked, ridgeSupport152_026_checked, ridgeSupport152_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
