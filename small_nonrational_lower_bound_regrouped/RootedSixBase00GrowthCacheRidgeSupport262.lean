module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport262Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 262 028 15
cert_ridgeSupport_suffix_decode_2 262 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 262 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 262 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 262 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 262 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 262 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 262 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 262 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 262 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 262 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 262 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 262 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 262 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 262 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 262 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 262 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 262 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 262 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 262 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 262 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 262 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 262 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 262 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 262 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 262 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 262 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 262 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 262 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 262
theorem ridgeTest_large_262 : ridgeTest 262 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport262_eq]
    simp only [ridgeSupport262_suffix_000, ridgeSupport262_suffix_001, ridgeSupport262_suffix_002, ridgeSupport262_suffix_003, ridgeSupport262_suffix_004, ridgeSupport262_suffix_005, ridgeSupport262_suffix_006, ridgeSupport262_suffix_007, ridgeSupport262_suffix_008, ridgeSupport262_suffix_009, ridgeSupport262_suffix_010, ridgeSupport262_suffix_011, ridgeSupport262_suffix_012, ridgeSupport262_suffix_013, ridgeSupport262_suffix_014, ridgeSupport262_suffix_015, ridgeSupport262_suffix_016, ridgeSupport262_suffix_017, ridgeSupport262_suffix_018, ridgeSupport262_suffix_019, ridgeSupport262_suffix_020, ridgeSupport262_suffix_021, ridgeSupport262_suffix_022, ridgeSupport262_suffix_023, ridgeSupport262_suffix_024, ridgeSupport262_suffix_025, ridgeSupport262_suffix_026, ridgeSupport262_suffix_027, ridgeSupport262_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport262_000_mask, ridgeSupport262_001_mask, ridgeSupport262_002_mask, ridgeSupport262_003_mask, ridgeSupport262_004_mask, ridgeSupport262_005_mask, ridgeSupport262_006_mask, ridgeSupport262_007_mask, ridgeSupport262_008_mask, ridgeSupport262_009_mask, ridgeSupport262_010_mask, ridgeSupport262_011_mask, ridgeSupport262_012_mask, ridgeSupport262_013_mask, ridgeSupport262_014_mask, ridgeSupport262_015_mask, ridgeSupport262_016_mask, ridgeSupport262_017_mask, ridgeSupport262_018_mask, ridgeSupport262_019_mask, ridgeSupport262_020_mask, ridgeSupport262_021_mask, ridgeSupport262_022_mask, ridgeSupport262_023_mask, ridgeSupport262_024_mask, ridgeSupport262_025_mask, ridgeSupport262_026_mask, ridgeSupport262_027_mask]
    decide +kernel
  · rw [ridgeSupport262_eq]
    simp only [ridgeSupport262_suffix_000, ridgeSupport262_suffix_001, ridgeSupport262_suffix_002, ridgeSupport262_suffix_003, ridgeSupport262_suffix_004, ridgeSupport262_suffix_005, ridgeSupport262_suffix_006, ridgeSupport262_suffix_007, ridgeSupport262_suffix_008, ridgeSupport262_suffix_009, ridgeSupport262_suffix_010, ridgeSupport262_suffix_011, ridgeSupport262_suffix_012, ridgeSupport262_suffix_013, ridgeSupport262_suffix_014, ridgeSupport262_suffix_015, ridgeSupport262_suffix_016, ridgeSupport262_suffix_017, ridgeSupport262_suffix_018, ridgeSupport262_suffix_019, ridgeSupport262_suffix_020, ridgeSupport262_suffix_021, ridgeSupport262_suffix_022, ridgeSupport262_suffix_023, ridgeSupport262_suffix_024, ridgeSupport262_suffix_025, ridgeSupport262_suffix_026, ridgeSupport262_suffix_027, ridgeSupport262_suffix_028, List.all_append, List.all_nil, ridgeSupport262_000_checked, ridgeSupport262_001_checked, ridgeSupport262_002_checked, ridgeSupport262_003_checked, ridgeSupport262_004_checked, ridgeSupport262_005_checked, ridgeSupport262_006_checked, ridgeSupport262_007_checked, ridgeSupport262_008_checked, ridgeSupport262_009_checked, ridgeSupport262_010_checked, ridgeSupport262_011_checked, ridgeSupport262_012_checked, ridgeSupport262_013_checked, ridgeSupport262_014_checked, ridgeSupport262_015_checked, ridgeSupport262_016_checked, ridgeSupport262_017_checked, ridgeSupport262_018_checked, ridgeSupport262_019_checked, ridgeSupport262_020_checked, ridgeSupport262_021_checked, ridgeSupport262_022_checked, ridgeSupport262_023_checked, ridgeSupport262_024_checked, ridgeSupport262_025_checked, ridgeSupport262_026_checked, ridgeSupport262_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
