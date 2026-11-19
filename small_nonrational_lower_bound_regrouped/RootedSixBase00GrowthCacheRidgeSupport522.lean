module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport522Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 522 028 15
cert_ridgeSupport_suffix_decode_2 522 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 522 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 522 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 522 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 522 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 522 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 522 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 522 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 522 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 522 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 522 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 522 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 522 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 522 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 522 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 522 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 522 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 522 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 522 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 522 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 522 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 522 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 522 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 522 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 522 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 522 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 522 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 522 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 522
theorem ridgeTest_large_522 : ridgeTest 522 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport522_eq]
    simp only [ridgeSupport522_suffix_000, ridgeSupport522_suffix_001, ridgeSupport522_suffix_002, ridgeSupport522_suffix_003, ridgeSupport522_suffix_004, ridgeSupport522_suffix_005, ridgeSupport522_suffix_006, ridgeSupport522_suffix_007, ridgeSupport522_suffix_008, ridgeSupport522_suffix_009, ridgeSupport522_suffix_010, ridgeSupport522_suffix_011, ridgeSupport522_suffix_012, ridgeSupport522_suffix_013, ridgeSupport522_suffix_014, ridgeSupport522_suffix_015, ridgeSupport522_suffix_016, ridgeSupport522_suffix_017, ridgeSupport522_suffix_018, ridgeSupport522_suffix_019, ridgeSupport522_suffix_020, ridgeSupport522_suffix_021, ridgeSupport522_suffix_022, ridgeSupport522_suffix_023, ridgeSupport522_suffix_024, ridgeSupport522_suffix_025, ridgeSupport522_suffix_026, ridgeSupport522_suffix_027, ridgeSupport522_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport522_000_mask, ridgeSupport522_001_mask, ridgeSupport522_002_mask, ridgeSupport522_003_mask, ridgeSupport522_004_mask, ridgeSupport522_005_mask, ridgeSupport522_006_mask, ridgeSupport522_007_mask, ridgeSupport522_008_mask, ridgeSupport522_009_mask, ridgeSupport522_010_mask, ridgeSupport522_011_mask, ridgeSupport522_012_mask, ridgeSupport522_013_mask, ridgeSupport522_014_mask, ridgeSupport522_015_mask, ridgeSupport522_016_mask, ridgeSupport522_017_mask, ridgeSupport522_018_mask, ridgeSupport522_019_mask, ridgeSupport522_020_mask, ridgeSupport522_021_mask, ridgeSupport522_022_mask, ridgeSupport522_023_mask, ridgeSupport522_024_mask, ridgeSupport522_025_mask, ridgeSupport522_026_mask, ridgeSupport522_027_mask]
    decide +kernel
  · rw [ridgeSupport522_eq]
    simp only [ridgeSupport522_suffix_000, ridgeSupport522_suffix_001, ridgeSupport522_suffix_002, ridgeSupport522_suffix_003, ridgeSupport522_suffix_004, ridgeSupport522_suffix_005, ridgeSupport522_suffix_006, ridgeSupport522_suffix_007, ridgeSupport522_suffix_008, ridgeSupport522_suffix_009, ridgeSupport522_suffix_010, ridgeSupport522_suffix_011, ridgeSupport522_suffix_012, ridgeSupport522_suffix_013, ridgeSupport522_suffix_014, ridgeSupport522_suffix_015, ridgeSupport522_suffix_016, ridgeSupport522_suffix_017, ridgeSupport522_suffix_018, ridgeSupport522_suffix_019, ridgeSupport522_suffix_020, ridgeSupport522_suffix_021, ridgeSupport522_suffix_022, ridgeSupport522_suffix_023, ridgeSupport522_suffix_024, ridgeSupport522_suffix_025, ridgeSupport522_suffix_026, ridgeSupport522_suffix_027, ridgeSupport522_suffix_028, List.all_append, List.all_nil, ridgeSupport522_000_checked, ridgeSupport522_001_checked, ridgeSupport522_002_checked, ridgeSupport522_003_checked, ridgeSupport522_004_checked, ridgeSupport522_005_checked, ridgeSupport522_006_checked, ridgeSupport522_007_checked, ridgeSupport522_008_checked, ridgeSupport522_009_checked, ridgeSupport522_010_checked, ridgeSupport522_011_checked, ridgeSupport522_012_checked, ridgeSupport522_013_checked, ridgeSupport522_014_checked, ridgeSupport522_015_checked, ridgeSupport522_016_checked, ridgeSupport522_017_checked, ridgeSupport522_018_checked, ridgeSupport522_019_checked, ridgeSupport522_020_checked, ridgeSupport522_021_checked, ridgeSupport522_022_checked, ridgeSupport522_023_checked, ridgeSupport522_024_checked, ridgeSupport522_025_checked, ridgeSupport522_026_checked, ridgeSupport522_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
