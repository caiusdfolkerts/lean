module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport164Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 164 028 15
cert_ridgeSupport_suffix_decode_2 164 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 164 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 164 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 164 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 164 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 164 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 164 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 164 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 164 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 164 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 164 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 164 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 164 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 164 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 164 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 164 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 164 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 164 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 164 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 164 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 164 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 164 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 164 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 164 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 164 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 164 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 164 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 164 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 164
theorem ridgeTest_large_164 : ridgeTest 164 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport164_eq]
    simp only [ridgeSupport164_suffix_000, ridgeSupport164_suffix_001, ridgeSupport164_suffix_002, ridgeSupport164_suffix_003, ridgeSupport164_suffix_004, ridgeSupport164_suffix_005, ridgeSupport164_suffix_006, ridgeSupport164_suffix_007, ridgeSupport164_suffix_008, ridgeSupport164_suffix_009, ridgeSupport164_suffix_010, ridgeSupport164_suffix_011, ridgeSupport164_suffix_012, ridgeSupport164_suffix_013, ridgeSupport164_suffix_014, ridgeSupport164_suffix_015, ridgeSupport164_suffix_016, ridgeSupport164_suffix_017, ridgeSupport164_suffix_018, ridgeSupport164_suffix_019, ridgeSupport164_suffix_020, ridgeSupport164_suffix_021, ridgeSupport164_suffix_022, ridgeSupport164_suffix_023, ridgeSupport164_suffix_024, ridgeSupport164_suffix_025, ridgeSupport164_suffix_026, ridgeSupport164_suffix_027, ridgeSupport164_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport164_000_mask, ridgeSupport164_001_mask, ridgeSupport164_002_mask, ridgeSupport164_003_mask, ridgeSupport164_004_mask, ridgeSupport164_005_mask, ridgeSupport164_006_mask, ridgeSupport164_007_mask, ridgeSupport164_008_mask, ridgeSupport164_009_mask, ridgeSupport164_010_mask, ridgeSupport164_011_mask, ridgeSupport164_012_mask, ridgeSupport164_013_mask, ridgeSupport164_014_mask, ridgeSupport164_015_mask, ridgeSupport164_016_mask, ridgeSupport164_017_mask, ridgeSupport164_018_mask, ridgeSupport164_019_mask, ridgeSupport164_020_mask, ridgeSupport164_021_mask, ridgeSupport164_022_mask, ridgeSupport164_023_mask, ridgeSupport164_024_mask, ridgeSupport164_025_mask, ridgeSupport164_026_mask, ridgeSupport164_027_mask]
    decide +kernel
  · rw [ridgeSupport164_eq]
    simp only [ridgeSupport164_suffix_000, ridgeSupport164_suffix_001, ridgeSupport164_suffix_002, ridgeSupport164_suffix_003, ridgeSupport164_suffix_004, ridgeSupport164_suffix_005, ridgeSupport164_suffix_006, ridgeSupport164_suffix_007, ridgeSupport164_suffix_008, ridgeSupport164_suffix_009, ridgeSupport164_suffix_010, ridgeSupport164_suffix_011, ridgeSupport164_suffix_012, ridgeSupport164_suffix_013, ridgeSupport164_suffix_014, ridgeSupport164_suffix_015, ridgeSupport164_suffix_016, ridgeSupport164_suffix_017, ridgeSupport164_suffix_018, ridgeSupport164_suffix_019, ridgeSupport164_suffix_020, ridgeSupport164_suffix_021, ridgeSupport164_suffix_022, ridgeSupport164_suffix_023, ridgeSupport164_suffix_024, ridgeSupport164_suffix_025, ridgeSupport164_suffix_026, ridgeSupport164_suffix_027, ridgeSupport164_suffix_028, List.all_append, List.all_nil, ridgeSupport164_000_checked, ridgeSupport164_001_checked, ridgeSupport164_002_checked, ridgeSupport164_003_checked, ridgeSupport164_004_checked, ridgeSupport164_005_checked, ridgeSupport164_006_checked, ridgeSupport164_007_checked, ridgeSupport164_008_checked, ridgeSupport164_009_checked, ridgeSupport164_010_checked, ridgeSupport164_011_checked, ridgeSupport164_012_checked, ridgeSupport164_013_checked, ridgeSupport164_014_checked, ridgeSupport164_015_checked, ridgeSupport164_016_checked, ridgeSupport164_017_checked, ridgeSupport164_018_checked, ridgeSupport164_019_checked, ridgeSupport164_020_checked, ridgeSupport164_021_checked, ridgeSupport164_022_checked, ridgeSupport164_023_checked, ridgeSupport164_024_checked, ridgeSupport164_025_checked, ridgeSupport164_026_checked, ridgeSupport164_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
