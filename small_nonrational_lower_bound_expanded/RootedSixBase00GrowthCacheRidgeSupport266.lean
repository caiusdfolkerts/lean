module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport266Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 266 028 15
cert_ridgeSupport_suffix_decode_2 266 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 266 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 266 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 266 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 266 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 266 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 266 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 266 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 266 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 266 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 266 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 266 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 266 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 266 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 266 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 266 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 266 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 266 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 266 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 266 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 266 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 266 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 266 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 266 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 266 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 266 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 266 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 266 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 266
theorem ridgeTest_large_266 : ridgeTest 266 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport266_eq]
    simp only [ridgeSupport266_suffix_000, ridgeSupport266_suffix_001, ridgeSupport266_suffix_002, ridgeSupport266_suffix_003, ridgeSupport266_suffix_004, ridgeSupport266_suffix_005, ridgeSupport266_suffix_006, ridgeSupport266_suffix_007, ridgeSupport266_suffix_008, ridgeSupport266_suffix_009, ridgeSupport266_suffix_010, ridgeSupport266_suffix_011, ridgeSupport266_suffix_012, ridgeSupport266_suffix_013, ridgeSupport266_suffix_014, ridgeSupport266_suffix_015, ridgeSupport266_suffix_016, ridgeSupport266_suffix_017, ridgeSupport266_suffix_018, ridgeSupport266_suffix_019, ridgeSupport266_suffix_020, ridgeSupport266_suffix_021, ridgeSupport266_suffix_022, ridgeSupport266_suffix_023, ridgeSupport266_suffix_024, ridgeSupport266_suffix_025, ridgeSupport266_suffix_026, ridgeSupport266_suffix_027, ridgeSupport266_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport266_000_mask, ridgeSupport266_001_mask, ridgeSupport266_002_mask, ridgeSupport266_003_mask, ridgeSupport266_004_mask, ridgeSupport266_005_mask, ridgeSupport266_006_mask, ridgeSupport266_007_mask, ridgeSupport266_008_mask, ridgeSupport266_009_mask, ridgeSupport266_010_mask, ridgeSupport266_011_mask, ridgeSupport266_012_mask, ridgeSupport266_013_mask, ridgeSupport266_014_mask, ridgeSupport266_015_mask, ridgeSupport266_016_mask, ridgeSupport266_017_mask, ridgeSupport266_018_mask, ridgeSupport266_019_mask, ridgeSupport266_020_mask, ridgeSupport266_021_mask, ridgeSupport266_022_mask, ridgeSupport266_023_mask, ridgeSupport266_024_mask, ridgeSupport266_025_mask, ridgeSupport266_026_mask, ridgeSupport266_027_mask]
    decide +kernel
  · rw [ridgeSupport266_eq]
    simp only [ridgeSupport266_suffix_000, ridgeSupport266_suffix_001, ridgeSupport266_suffix_002, ridgeSupport266_suffix_003, ridgeSupport266_suffix_004, ridgeSupport266_suffix_005, ridgeSupport266_suffix_006, ridgeSupport266_suffix_007, ridgeSupport266_suffix_008, ridgeSupport266_suffix_009, ridgeSupport266_suffix_010, ridgeSupport266_suffix_011, ridgeSupport266_suffix_012, ridgeSupport266_suffix_013, ridgeSupport266_suffix_014, ridgeSupport266_suffix_015, ridgeSupport266_suffix_016, ridgeSupport266_suffix_017, ridgeSupport266_suffix_018, ridgeSupport266_suffix_019, ridgeSupport266_suffix_020, ridgeSupport266_suffix_021, ridgeSupport266_suffix_022, ridgeSupport266_suffix_023, ridgeSupport266_suffix_024, ridgeSupport266_suffix_025, ridgeSupport266_suffix_026, ridgeSupport266_suffix_027, ridgeSupport266_suffix_028, List.all_append, List.all_nil, ridgeSupport266_000_checked, ridgeSupport266_001_checked, ridgeSupport266_002_checked, ridgeSupport266_003_checked, ridgeSupport266_004_checked, ridgeSupport266_005_checked, ridgeSupport266_006_checked, ridgeSupport266_007_checked, ridgeSupport266_008_checked, ridgeSupport266_009_checked, ridgeSupport266_010_checked, ridgeSupport266_011_checked, ridgeSupport266_012_checked, ridgeSupport266_013_checked, ridgeSupport266_014_checked, ridgeSupport266_015_checked, ridgeSupport266_016_checked, ridgeSupport266_017_checked, ridgeSupport266_018_checked, ridgeSupport266_019_checked, ridgeSupport266_020_checked, ridgeSupport266_021_checked, ridgeSupport266_022_checked, ridgeSupport266_023_checked, ridgeSupport266_024_checked, ridgeSupport266_025_checked, ridgeSupport266_026_checked, ridgeSupport266_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
