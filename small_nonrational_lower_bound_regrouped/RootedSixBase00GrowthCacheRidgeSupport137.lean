module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport137Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 137 028 15
cert_ridgeSupport_suffix_decode_2 137 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 137 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 137 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 137 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 137 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 137 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 137 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 137 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 137 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 137 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 137 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 137 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 137 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 137 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 137 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 137 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 137 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 137 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 137 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 137 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 137 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 137 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 137 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 137 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 137 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 137 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 137 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 137 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 137
theorem ridgeTest_large_137 : ridgeTest 137 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport137_eq]
    simp only [ridgeSupport137_suffix_000, ridgeSupport137_suffix_001, ridgeSupport137_suffix_002, ridgeSupport137_suffix_003, ridgeSupport137_suffix_004, ridgeSupport137_suffix_005, ridgeSupport137_suffix_006, ridgeSupport137_suffix_007, ridgeSupport137_suffix_008, ridgeSupport137_suffix_009, ridgeSupport137_suffix_010, ridgeSupport137_suffix_011, ridgeSupport137_suffix_012, ridgeSupport137_suffix_013, ridgeSupport137_suffix_014, ridgeSupport137_suffix_015, ridgeSupport137_suffix_016, ridgeSupport137_suffix_017, ridgeSupport137_suffix_018, ridgeSupport137_suffix_019, ridgeSupport137_suffix_020, ridgeSupport137_suffix_021, ridgeSupport137_suffix_022, ridgeSupport137_suffix_023, ridgeSupport137_suffix_024, ridgeSupport137_suffix_025, ridgeSupport137_suffix_026, ridgeSupport137_suffix_027, ridgeSupport137_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport137_000_mask, ridgeSupport137_001_mask, ridgeSupport137_002_mask, ridgeSupport137_003_mask, ridgeSupport137_004_mask, ridgeSupport137_005_mask, ridgeSupport137_006_mask, ridgeSupport137_007_mask, ridgeSupport137_008_mask, ridgeSupport137_009_mask, ridgeSupport137_010_mask, ridgeSupport137_011_mask, ridgeSupport137_012_mask, ridgeSupport137_013_mask, ridgeSupport137_014_mask, ridgeSupport137_015_mask, ridgeSupport137_016_mask, ridgeSupport137_017_mask, ridgeSupport137_018_mask, ridgeSupport137_019_mask, ridgeSupport137_020_mask, ridgeSupport137_021_mask, ridgeSupport137_022_mask, ridgeSupport137_023_mask, ridgeSupport137_024_mask, ridgeSupport137_025_mask, ridgeSupport137_026_mask, ridgeSupport137_027_mask]
    decide +kernel
  · rw [ridgeSupport137_eq]
    simp only [ridgeSupport137_suffix_000, ridgeSupport137_suffix_001, ridgeSupport137_suffix_002, ridgeSupport137_suffix_003, ridgeSupport137_suffix_004, ridgeSupport137_suffix_005, ridgeSupport137_suffix_006, ridgeSupport137_suffix_007, ridgeSupport137_suffix_008, ridgeSupport137_suffix_009, ridgeSupport137_suffix_010, ridgeSupport137_suffix_011, ridgeSupport137_suffix_012, ridgeSupport137_suffix_013, ridgeSupport137_suffix_014, ridgeSupport137_suffix_015, ridgeSupport137_suffix_016, ridgeSupport137_suffix_017, ridgeSupport137_suffix_018, ridgeSupport137_suffix_019, ridgeSupport137_suffix_020, ridgeSupport137_suffix_021, ridgeSupport137_suffix_022, ridgeSupport137_suffix_023, ridgeSupport137_suffix_024, ridgeSupport137_suffix_025, ridgeSupport137_suffix_026, ridgeSupport137_suffix_027, ridgeSupport137_suffix_028, List.all_append, List.all_nil, ridgeSupport137_000_checked, ridgeSupport137_001_checked, ridgeSupport137_002_checked, ridgeSupport137_003_checked, ridgeSupport137_004_checked, ridgeSupport137_005_checked, ridgeSupport137_006_checked, ridgeSupport137_007_checked, ridgeSupport137_008_checked, ridgeSupport137_009_checked, ridgeSupport137_010_checked, ridgeSupport137_011_checked, ridgeSupport137_012_checked, ridgeSupport137_013_checked, ridgeSupport137_014_checked, ridgeSupport137_015_checked, ridgeSupport137_016_checked, ridgeSupport137_017_checked, ridgeSupport137_018_checked, ridgeSupport137_019_checked, ridgeSupport137_020_checked, ridgeSupport137_021_checked, ridgeSupport137_022_checked, ridgeSupport137_023_checked, ridgeSupport137_024_checked, ridgeSupport137_025_checked, ridgeSupport137_026_checked, ridgeSupport137_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
