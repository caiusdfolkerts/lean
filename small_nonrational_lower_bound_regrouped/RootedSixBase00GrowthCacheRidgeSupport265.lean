module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport265Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 265 028 15
cert_ridgeSupport_suffix_decode_2 265 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 265 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 265 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 265 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 265 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 265 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 265 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 265 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 265 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 265 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 265 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 265 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 265 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 265 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 265 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 265 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 265 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 265 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 265 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 265 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 265 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 265 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 265 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 265 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 265 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 265 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 265 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 265 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 265
theorem ridgeTest_large_265 : ridgeTest 265 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport265_eq]
    simp only [ridgeSupport265_suffix_000, ridgeSupport265_suffix_001, ridgeSupport265_suffix_002, ridgeSupport265_suffix_003, ridgeSupport265_suffix_004, ridgeSupport265_suffix_005, ridgeSupport265_suffix_006, ridgeSupport265_suffix_007, ridgeSupport265_suffix_008, ridgeSupport265_suffix_009, ridgeSupport265_suffix_010, ridgeSupport265_suffix_011, ridgeSupport265_suffix_012, ridgeSupport265_suffix_013, ridgeSupport265_suffix_014, ridgeSupport265_suffix_015, ridgeSupport265_suffix_016, ridgeSupport265_suffix_017, ridgeSupport265_suffix_018, ridgeSupport265_suffix_019, ridgeSupport265_suffix_020, ridgeSupport265_suffix_021, ridgeSupport265_suffix_022, ridgeSupport265_suffix_023, ridgeSupport265_suffix_024, ridgeSupport265_suffix_025, ridgeSupport265_suffix_026, ridgeSupport265_suffix_027, ridgeSupport265_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport265_000_mask, ridgeSupport265_001_mask, ridgeSupport265_002_mask, ridgeSupport265_003_mask, ridgeSupport265_004_mask, ridgeSupport265_005_mask, ridgeSupport265_006_mask, ridgeSupport265_007_mask, ridgeSupport265_008_mask, ridgeSupport265_009_mask, ridgeSupport265_010_mask, ridgeSupport265_011_mask, ridgeSupport265_012_mask, ridgeSupport265_013_mask, ridgeSupport265_014_mask, ridgeSupport265_015_mask, ridgeSupport265_016_mask, ridgeSupport265_017_mask, ridgeSupport265_018_mask, ridgeSupport265_019_mask, ridgeSupport265_020_mask, ridgeSupport265_021_mask, ridgeSupport265_022_mask, ridgeSupport265_023_mask, ridgeSupport265_024_mask, ridgeSupport265_025_mask, ridgeSupport265_026_mask, ridgeSupport265_027_mask]
    decide +kernel
  · rw [ridgeSupport265_eq]
    simp only [ridgeSupport265_suffix_000, ridgeSupport265_suffix_001, ridgeSupport265_suffix_002, ridgeSupport265_suffix_003, ridgeSupport265_suffix_004, ridgeSupport265_suffix_005, ridgeSupport265_suffix_006, ridgeSupport265_suffix_007, ridgeSupport265_suffix_008, ridgeSupport265_suffix_009, ridgeSupport265_suffix_010, ridgeSupport265_suffix_011, ridgeSupport265_suffix_012, ridgeSupport265_suffix_013, ridgeSupport265_suffix_014, ridgeSupport265_suffix_015, ridgeSupport265_suffix_016, ridgeSupport265_suffix_017, ridgeSupport265_suffix_018, ridgeSupport265_suffix_019, ridgeSupport265_suffix_020, ridgeSupport265_suffix_021, ridgeSupport265_suffix_022, ridgeSupport265_suffix_023, ridgeSupport265_suffix_024, ridgeSupport265_suffix_025, ridgeSupport265_suffix_026, ridgeSupport265_suffix_027, ridgeSupport265_suffix_028, List.all_append, List.all_nil, ridgeSupport265_000_checked, ridgeSupport265_001_checked, ridgeSupport265_002_checked, ridgeSupport265_003_checked, ridgeSupport265_004_checked, ridgeSupport265_005_checked, ridgeSupport265_006_checked, ridgeSupport265_007_checked, ridgeSupport265_008_checked, ridgeSupport265_009_checked, ridgeSupport265_010_checked, ridgeSupport265_011_checked, ridgeSupport265_012_checked, ridgeSupport265_013_checked, ridgeSupport265_014_checked, ridgeSupport265_015_checked, ridgeSupport265_016_checked, ridgeSupport265_017_checked, ridgeSupport265_018_checked, ridgeSupport265_019_checked, ridgeSupport265_020_checked, ridgeSupport265_021_checked, ridgeSupport265_022_checked, ridgeSupport265_023_checked, ridgeSupport265_024_checked, ridgeSupport265_025_checked, ridgeSupport265_026_checked, ridgeSupport265_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
