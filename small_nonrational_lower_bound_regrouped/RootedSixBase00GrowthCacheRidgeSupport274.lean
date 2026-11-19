module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport274Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 274 028 15
cert_ridgeSupport_suffix_decode_2 274 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 274 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 274 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 274 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 274 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 274 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 274 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 274 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 274 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 274 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 274 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 274 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 274 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 274 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 274 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 274 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 274 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 274 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 274 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 274 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 274 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 274 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 274 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 274 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 274 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 274 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 274 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 274 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 274
theorem ridgeTest_large_274 : ridgeTest 274 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport274_eq]
    simp only [ridgeSupport274_suffix_000, ridgeSupport274_suffix_001, ridgeSupport274_suffix_002, ridgeSupport274_suffix_003, ridgeSupport274_suffix_004, ridgeSupport274_suffix_005, ridgeSupport274_suffix_006, ridgeSupport274_suffix_007, ridgeSupport274_suffix_008, ridgeSupport274_suffix_009, ridgeSupport274_suffix_010, ridgeSupport274_suffix_011, ridgeSupport274_suffix_012, ridgeSupport274_suffix_013, ridgeSupport274_suffix_014, ridgeSupport274_suffix_015, ridgeSupport274_suffix_016, ridgeSupport274_suffix_017, ridgeSupport274_suffix_018, ridgeSupport274_suffix_019, ridgeSupport274_suffix_020, ridgeSupport274_suffix_021, ridgeSupport274_suffix_022, ridgeSupport274_suffix_023, ridgeSupport274_suffix_024, ridgeSupport274_suffix_025, ridgeSupport274_suffix_026, ridgeSupport274_suffix_027, ridgeSupport274_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport274_000_mask, ridgeSupport274_001_mask, ridgeSupport274_002_mask, ridgeSupport274_003_mask, ridgeSupport274_004_mask, ridgeSupport274_005_mask, ridgeSupport274_006_mask, ridgeSupport274_007_mask, ridgeSupport274_008_mask, ridgeSupport274_009_mask, ridgeSupport274_010_mask, ridgeSupport274_011_mask, ridgeSupport274_012_mask, ridgeSupport274_013_mask, ridgeSupport274_014_mask, ridgeSupport274_015_mask, ridgeSupport274_016_mask, ridgeSupport274_017_mask, ridgeSupport274_018_mask, ridgeSupport274_019_mask, ridgeSupport274_020_mask, ridgeSupport274_021_mask, ridgeSupport274_022_mask, ridgeSupport274_023_mask, ridgeSupport274_024_mask, ridgeSupport274_025_mask, ridgeSupport274_026_mask, ridgeSupport274_027_mask]
    decide +kernel
  · rw [ridgeSupport274_eq]
    simp only [ridgeSupport274_suffix_000, ridgeSupport274_suffix_001, ridgeSupport274_suffix_002, ridgeSupport274_suffix_003, ridgeSupport274_suffix_004, ridgeSupport274_suffix_005, ridgeSupport274_suffix_006, ridgeSupport274_suffix_007, ridgeSupport274_suffix_008, ridgeSupport274_suffix_009, ridgeSupport274_suffix_010, ridgeSupport274_suffix_011, ridgeSupport274_suffix_012, ridgeSupport274_suffix_013, ridgeSupport274_suffix_014, ridgeSupport274_suffix_015, ridgeSupport274_suffix_016, ridgeSupport274_suffix_017, ridgeSupport274_suffix_018, ridgeSupport274_suffix_019, ridgeSupport274_suffix_020, ridgeSupport274_suffix_021, ridgeSupport274_suffix_022, ridgeSupport274_suffix_023, ridgeSupport274_suffix_024, ridgeSupport274_suffix_025, ridgeSupport274_suffix_026, ridgeSupport274_suffix_027, ridgeSupport274_suffix_028, List.all_append, List.all_nil, ridgeSupport274_000_checked, ridgeSupport274_001_checked, ridgeSupport274_002_checked, ridgeSupport274_003_checked, ridgeSupport274_004_checked, ridgeSupport274_005_checked, ridgeSupport274_006_checked, ridgeSupport274_007_checked, ridgeSupport274_008_checked, ridgeSupport274_009_checked, ridgeSupport274_010_checked, ridgeSupport274_011_checked, ridgeSupport274_012_checked, ridgeSupport274_013_checked, ridgeSupport274_014_checked, ridgeSupport274_015_checked, ridgeSupport274_016_checked, ridgeSupport274_017_checked, ridgeSupport274_018_checked, ridgeSupport274_019_checked, ridgeSupport274_020_checked, ridgeSupport274_021_checked, ridgeSupport274_022_checked, ridgeSupport274_023_checked, ridgeSupport274_024_checked, ridgeSupport274_025_checked, ridgeSupport274_026_checked, ridgeSupport274_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
