module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport259Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 259 028 15
cert_ridgeSupport_suffix_decode_2 259 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 259 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 259 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 259 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 259 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 259 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 259 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 259 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 259 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 259 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 259 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 259 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 259 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 259 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 259 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 259 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 259 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 259 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 259 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 259 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 259 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 259 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 259 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 259 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 259 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 259 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 259 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 259 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 259
theorem ridgeTest_large_259 : ridgeTest 259 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport259_eq]
    simp only [ridgeSupport259_suffix_000, ridgeSupport259_suffix_001, ridgeSupport259_suffix_002, ridgeSupport259_suffix_003, ridgeSupport259_suffix_004, ridgeSupport259_suffix_005, ridgeSupport259_suffix_006, ridgeSupport259_suffix_007, ridgeSupport259_suffix_008, ridgeSupport259_suffix_009, ridgeSupport259_suffix_010, ridgeSupport259_suffix_011, ridgeSupport259_suffix_012, ridgeSupport259_suffix_013, ridgeSupport259_suffix_014, ridgeSupport259_suffix_015, ridgeSupport259_suffix_016, ridgeSupport259_suffix_017, ridgeSupport259_suffix_018, ridgeSupport259_suffix_019, ridgeSupport259_suffix_020, ridgeSupport259_suffix_021, ridgeSupport259_suffix_022, ridgeSupport259_suffix_023, ridgeSupport259_suffix_024, ridgeSupport259_suffix_025, ridgeSupport259_suffix_026, ridgeSupport259_suffix_027, ridgeSupport259_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport259_000_mask, ridgeSupport259_001_mask, ridgeSupport259_002_mask, ridgeSupport259_003_mask, ridgeSupport259_004_mask, ridgeSupport259_005_mask, ridgeSupport259_006_mask, ridgeSupport259_007_mask, ridgeSupport259_008_mask, ridgeSupport259_009_mask, ridgeSupport259_010_mask, ridgeSupport259_011_mask, ridgeSupport259_012_mask, ridgeSupport259_013_mask, ridgeSupport259_014_mask, ridgeSupport259_015_mask, ridgeSupport259_016_mask, ridgeSupport259_017_mask, ridgeSupport259_018_mask, ridgeSupport259_019_mask, ridgeSupport259_020_mask, ridgeSupport259_021_mask, ridgeSupport259_022_mask, ridgeSupport259_023_mask, ridgeSupport259_024_mask, ridgeSupport259_025_mask, ridgeSupport259_026_mask, ridgeSupport259_027_mask]
    decide +kernel
  · rw [ridgeSupport259_eq]
    simp only [ridgeSupport259_suffix_000, ridgeSupport259_suffix_001, ridgeSupport259_suffix_002, ridgeSupport259_suffix_003, ridgeSupport259_suffix_004, ridgeSupport259_suffix_005, ridgeSupport259_suffix_006, ridgeSupport259_suffix_007, ridgeSupport259_suffix_008, ridgeSupport259_suffix_009, ridgeSupport259_suffix_010, ridgeSupport259_suffix_011, ridgeSupport259_suffix_012, ridgeSupport259_suffix_013, ridgeSupport259_suffix_014, ridgeSupport259_suffix_015, ridgeSupport259_suffix_016, ridgeSupport259_suffix_017, ridgeSupport259_suffix_018, ridgeSupport259_suffix_019, ridgeSupport259_suffix_020, ridgeSupport259_suffix_021, ridgeSupport259_suffix_022, ridgeSupport259_suffix_023, ridgeSupport259_suffix_024, ridgeSupport259_suffix_025, ridgeSupport259_suffix_026, ridgeSupport259_suffix_027, ridgeSupport259_suffix_028, List.all_append, List.all_nil, ridgeSupport259_000_checked, ridgeSupport259_001_checked, ridgeSupport259_002_checked, ridgeSupport259_003_checked, ridgeSupport259_004_checked, ridgeSupport259_005_checked, ridgeSupport259_006_checked, ridgeSupport259_007_checked, ridgeSupport259_008_checked, ridgeSupport259_009_checked, ridgeSupport259_010_checked, ridgeSupport259_011_checked, ridgeSupport259_012_checked, ridgeSupport259_013_checked, ridgeSupport259_014_checked, ridgeSupport259_015_checked, ridgeSupport259_016_checked, ridgeSupport259_017_checked, ridgeSupport259_018_checked, ridgeSupport259_019_checked, ridgeSupport259_020_checked, ridgeSupport259_021_checked, ridgeSupport259_022_checked, ridgeSupport259_023_checked, ridgeSupport259_024_checked, ridgeSupport259_025_checked, ridgeSupport259_026_checked, ridgeSupport259_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
