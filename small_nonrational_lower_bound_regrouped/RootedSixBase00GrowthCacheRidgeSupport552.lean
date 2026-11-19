module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport552Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 552 028 15
cert_ridgeSupport_suffix_decode_2 552 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 552 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 552 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 552 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 552 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 552 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 552 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 552 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 552 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 552 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 552 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 552 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 552 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 552 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 552 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 552 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 552 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 552 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 552 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 552 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 552 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 552 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 552 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 552 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 552 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 552 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 552 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 552 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 552
theorem ridgeTest_large_552 : ridgeTest 552 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport552_eq]
    simp only [ridgeSupport552_suffix_000, ridgeSupport552_suffix_001, ridgeSupport552_suffix_002, ridgeSupport552_suffix_003, ridgeSupport552_suffix_004, ridgeSupport552_suffix_005, ridgeSupport552_suffix_006, ridgeSupport552_suffix_007, ridgeSupport552_suffix_008, ridgeSupport552_suffix_009, ridgeSupport552_suffix_010, ridgeSupport552_suffix_011, ridgeSupport552_suffix_012, ridgeSupport552_suffix_013, ridgeSupport552_suffix_014, ridgeSupport552_suffix_015, ridgeSupport552_suffix_016, ridgeSupport552_suffix_017, ridgeSupport552_suffix_018, ridgeSupport552_suffix_019, ridgeSupport552_suffix_020, ridgeSupport552_suffix_021, ridgeSupport552_suffix_022, ridgeSupport552_suffix_023, ridgeSupport552_suffix_024, ridgeSupport552_suffix_025, ridgeSupport552_suffix_026, ridgeSupport552_suffix_027, ridgeSupport552_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport552_000_mask, ridgeSupport552_001_mask, ridgeSupport552_002_mask, ridgeSupport552_003_mask, ridgeSupport552_004_mask, ridgeSupport552_005_mask, ridgeSupport552_006_mask, ridgeSupport552_007_mask, ridgeSupport552_008_mask, ridgeSupport552_009_mask, ridgeSupport552_010_mask, ridgeSupport552_011_mask, ridgeSupport552_012_mask, ridgeSupport552_013_mask, ridgeSupport552_014_mask, ridgeSupport552_015_mask, ridgeSupport552_016_mask, ridgeSupport552_017_mask, ridgeSupport552_018_mask, ridgeSupport552_019_mask, ridgeSupport552_020_mask, ridgeSupport552_021_mask, ridgeSupport552_022_mask, ridgeSupport552_023_mask, ridgeSupport552_024_mask, ridgeSupport552_025_mask, ridgeSupport552_026_mask, ridgeSupport552_027_mask]
    decide +kernel
  · rw [ridgeSupport552_eq]
    simp only [ridgeSupport552_suffix_000, ridgeSupport552_suffix_001, ridgeSupport552_suffix_002, ridgeSupport552_suffix_003, ridgeSupport552_suffix_004, ridgeSupport552_suffix_005, ridgeSupport552_suffix_006, ridgeSupport552_suffix_007, ridgeSupport552_suffix_008, ridgeSupport552_suffix_009, ridgeSupport552_suffix_010, ridgeSupport552_suffix_011, ridgeSupport552_suffix_012, ridgeSupport552_suffix_013, ridgeSupport552_suffix_014, ridgeSupport552_suffix_015, ridgeSupport552_suffix_016, ridgeSupport552_suffix_017, ridgeSupport552_suffix_018, ridgeSupport552_suffix_019, ridgeSupport552_suffix_020, ridgeSupport552_suffix_021, ridgeSupport552_suffix_022, ridgeSupport552_suffix_023, ridgeSupport552_suffix_024, ridgeSupport552_suffix_025, ridgeSupport552_suffix_026, ridgeSupport552_suffix_027, ridgeSupport552_suffix_028, List.all_append, List.all_nil, ridgeSupport552_000_checked, ridgeSupport552_001_checked, ridgeSupport552_002_checked, ridgeSupport552_003_checked, ridgeSupport552_004_checked, ridgeSupport552_005_checked, ridgeSupport552_006_checked, ridgeSupport552_007_checked, ridgeSupport552_008_checked, ridgeSupport552_009_checked, ridgeSupport552_010_checked, ridgeSupport552_011_checked, ridgeSupport552_012_checked, ridgeSupport552_013_checked, ridgeSupport552_014_checked, ridgeSupport552_015_checked, ridgeSupport552_016_checked, ridgeSupport552_017_checked, ridgeSupport552_018_checked, ridgeSupport552_019_checked, ridgeSupport552_020_checked, ridgeSupport552_021_checked, ridgeSupport552_022_checked, ridgeSupport552_023_checked, ridgeSupport552_024_checked, ridgeSupport552_025_checked, ridgeSupport552_026_checked, ridgeSupport552_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
