module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport134Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 134 028 15
cert_ridgeSupport_suffix_decode_2 134 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 134 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 134 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 134 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 134 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 134 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 134 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 134 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 134 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 134 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 134 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 134 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 134 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 134 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 134 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 134 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 134 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 134 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 134 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 134 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 134 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 134 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 134 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 134 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 134 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 134 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 134 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 134 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 134
theorem ridgeTest_large_134 : ridgeTest 134 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport134_eq]
    simp only [ridgeSupport134_suffix_000, ridgeSupport134_suffix_001, ridgeSupport134_suffix_002, ridgeSupport134_suffix_003, ridgeSupport134_suffix_004, ridgeSupport134_suffix_005, ridgeSupport134_suffix_006, ridgeSupport134_suffix_007, ridgeSupport134_suffix_008, ridgeSupport134_suffix_009, ridgeSupport134_suffix_010, ridgeSupport134_suffix_011, ridgeSupport134_suffix_012, ridgeSupport134_suffix_013, ridgeSupport134_suffix_014, ridgeSupport134_suffix_015, ridgeSupport134_suffix_016, ridgeSupport134_suffix_017, ridgeSupport134_suffix_018, ridgeSupport134_suffix_019, ridgeSupport134_suffix_020, ridgeSupport134_suffix_021, ridgeSupport134_suffix_022, ridgeSupport134_suffix_023, ridgeSupport134_suffix_024, ridgeSupport134_suffix_025, ridgeSupport134_suffix_026, ridgeSupport134_suffix_027, ridgeSupport134_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport134_000_mask, ridgeSupport134_001_mask, ridgeSupport134_002_mask, ridgeSupport134_003_mask, ridgeSupport134_004_mask, ridgeSupport134_005_mask, ridgeSupport134_006_mask, ridgeSupport134_007_mask, ridgeSupport134_008_mask, ridgeSupport134_009_mask, ridgeSupport134_010_mask, ridgeSupport134_011_mask, ridgeSupport134_012_mask, ridgeSupport134_013_mask, ridgeSupport134_014_mask, ridgeSupport134_015_mask, ridgeSupport134_016_mask, ridgeSupport134_017_mask, ridgeSupport134_018_mask, ridgeSupport134_019_mask, ridgeSupport134_020_mask, ridgeSupport134_021_mask, ridgeSupport134_022_mask, ridgeSupport134_023_mask, ridgeSupport134_024_mask, ridgeSupport134_025_mask, ridgeSupport134_026_mask, ridgeSupport134_027_mask]
    decide +kernel
  · rw [ridgeSupport134_eq]
    simp only [ridgeSupport134_suffix_000, ridgeSupport134_suffix_001, ridgeSupport134_suffix_002, ridgeSupport134_suffix_003, ridgeSupport134_suffix_004, ridgeSupport134_suffix_005, ridgeSupport134_suffix_006, ridgeSupport134_suffix_007, ridgeSupport134_suffix_008, ridgeSupport134_suffix_009, ridgeSupport134_suffix_010, ridgeSupport134_suffix_011, ridgeSupport134_suffix_012, ridgeSupport134_suffix_013, ridgeSupport134_suffix_014, ridgeSupport134_suffix_015, ridgeSupport134_suffix_016, ridgeSupport134_suffix_017, ridgeSupport134_suffix_018, ridgeSupport134_suffix_019, ridgeSupport134_suffix_020, ridgeSupport134_suffix_021, ridgeSupport134_suffix_022, ridgeSupport134_suffix_023, ridgeSupport134_suffix_024, ridgeSupport134_suffix_025, ridgeSupport134_suffix_026, ridgeSupport134_suffix_027, ridgeSupport134_suffix_028, List.all_append, List.all_nil, ridgeSupport134_000_checked, ridgeSupport134_001_checked, ridgeSupport134_002_checked, ridgeSupport134_003_checked, ridgeSupport134_004_checked, ridgeSupport134_005_checked, ridgeSupport134_006_checked, ridgeSupport134_007_checked, ridgeSupport134_008_checked, ridgeSupport134_009_checked, ridgeSupport134_010_checked, ridgeSupport134_011_checked, ridgeSupport134_012_checked, ridgeSupport134_013_checked, ridgeSupport134_014_checked, ridgeSupport134_015_checked, ridgeSupport134_016_checked, ridgeSupport134_017_checked, ridgeSupport134_018_checked, ridgeSupport134_019_checked, ridgeSupport134_020_checked, ridgeSupport134_021_checked, ridgeSupport134_022_checked, ridgeSupport134_023_checked, ridgeSupport134_024_checked, ridgeSupport134_025_checked, ridgeSupport134_026_checked, ridgeSupport134_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
