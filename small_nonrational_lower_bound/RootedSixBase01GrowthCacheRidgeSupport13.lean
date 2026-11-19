module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport13Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 13 034 14
cert_ridgeSupport_suffix_decode_2 13 033 14 5 5 034 034 0
cert_ridgeSupport_suffix_decode_2 13 032 14 37 32 034 033 5
cert_ridgeSupport_suffix_decode_2 13 031 14 69 32 034 032 37
cert_ridgeSupport_suffix_decode_2 13 030 14 101 32 034 031 69
cert_ridgeSupport_suffix_decode_2 13 029 14 133 32 034 030 101
cert_ridgeSupport_suffix_decode_2 13 028 14 165 32 034 029 133
cert_ridgeSupport_suffix_decode_2 13 027 14 197 32 034 028 165
cert_ridgeSupport_suffix_decode_2 13 026 14 229 32 034 027 197
cert_ridgeSupport_suffix_decode_2 13 025 14 261 32 034 026 229
cert_ridgeSupport_suffix_decode_2 13 024 14 293 32 034 025 261
cert_ridgeSupport_suffix_decode_2 13 023 14 325 32 034 024 293
cert_ridgeSupport_suffix_decode_2 13 022 14 357 32 034 023 325
cert_ridgeSupport_suffix_decode_2 13 021 14 389 32 034 022 357
cert_ridgeSupport_suffix_decode_2 13 020 14 421 32 034 021 389
cert_ridgeSupport_suffix_decode_2 13 019 14 453 32 034 020 421
cert_ridgeSupport_suffix_decode_2 13 018 14 485 32 034 019 453
cert_ridgeSupport_suffix_decode_2 13 017 14 517 32 034 018 485
cert_ridgeSupport_suffix_decode_2 13 016 14 549 32 034 017 517
cert_ridgeSupport_suffix_decode_2 13 015 14 581 32 034 016 549
cert_ridgeSupport_suffix_decode_2 13 014 14 613 32 034 015 581
cert_ridgeSupport_suffix_decode_2 13 013 14 645 32 034 014 613
cert_ridgeSupport_suffix_decode_2 13 012 14 677 32 034 013 645
cert_ridgeSupport_suffix_decode_2 13 011 14 709 32 034 012 677
cert_ridgeSupport_suffix_decode_2 13 010 14 741 32 034 011 709
cert_ridgeSupport_suffix_decode_2 13 009 14 773 32 034 010 741
cert_ridgeSupport_suffix_decode_2 13 008 14 805 32 034 009 773
cert_ridgeSupport_suffix_decode_2 13 007 14 837 32 034 008 805
cert_ridgeSupport_suffix_decode_2 13 006 14 869 32 034 007 837
cert_ridgeSupport_suffix_decode_2 13 005 14 901 32 034 006 869
cert_ridgeSupport_suffix_decode_2 13 004 14 933 32 034 005 901
cert_ridgeSupport_suffix_decode_2 13 003 14 965 32 034 004 933
cert_ridgeSupport_suffix_decode_2 13 002 14 997 32 034 003 965
cert_ridgeSupport_suffix_decode_2 13 001 14 1029 32 034 002 997
cert_ridgeSupport_suffix_decode_2 13 000 14 1061 32 034 001 1029
cert_ridgeSupport_eq_3 13
theorem ridgeTest_large_13 : ridgeTest 13 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport13_eq]
    simp only [ridgeSupport13_suffix_000, ridgeSupport13_suffix_001, ridgeSupport13_suffix_002, ridgeSupport13_suffix_003, ridgeSupport13_suffix_004, ridgeSupport13_suffix_005, ridgeSupport13_suffix_006, ridgeSupport13_suffix_007, ridgeSupport13_suffix_008, ridgeSupport13_suffix_009, ridgeSupport13_suffix_010, ridgeSupport13_suffix_011, ridgeSupport13_suffix_012, ridgeSupport13_suffix_013, ridgeSupport13_suffix_014, ridgeSupport13_suffix_015, ridgeSupport13_suffix_016, ridgeSupport13_suffix_017, ridgeSupport13_suffix_018, ridgeSupport13_suffix_019, ridgeSupport13_suffix_020, ridgeSupport13_suffix_021, ridgeSupport13_suffix_022, ridgeSupport13_suffix_023, ridgeSupport13_suffix_024, ridgeSupport13_suffix_025, ridgeSupport13_suffix_026, ridgeSupport13_suffix_027, ridgeSupport13_suffix_028, ridgeSupport13_suffix_029, ridgeSupport13_suffix_030, ridgeSupport13_suffix_031, ridgeSupport13_suffix_032, ridgeSupport13_suffix_033, ridgeSupport13_suffix_034, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport13_000_mask, ridgeSupport13_001_mask, ridgeSupport13_002_mask, ridgeSupport13_003_mask, ridgeSupport13_004_mask, ridgeSupport13_005_mask, ridgeSupport13_006_mask, ridgeSupport13_007_mask, ridgeSupport13_008_mask, ridgeSupport13_009_mask, ridgeSupport13_010_mask, ridgeSupport13_011_mask, ridgeSupport13_012_mask, ridgeSupport13_013_mask, ridgeSupport13_014_mask, ridgeSupport13_015_mask, ridgeSupport13_016_mask, ridgeSupport13_017_mask, ridgeSupport13_018_mask, ridgeSupport13_019_mask, ridgeSupport13_020_mask, ridgeSupport13_021_mask, ridgeSupport13_022_mask, ridgeSupport13_023_mask, ridgeSupport13_024_mask, ridgeSupport13_025_mask, ridgeSupport13_026_mask, ridgeSupport13_027_mask, ridgeSupport13_028_mask, ridgeSupport13_029_mask, ridgeSupport13_030_mask, ridgeSupport13_031_mask, ridgeSupport13_032_mask, ridgeSupport13_033_mask]
    decide +kernel
  · rw [ridgeSupport13_eq]
    simp only [ridgeSupport13_suffix_000, ridgeSupport13_suffix_001, ridgeSupport13_suffix_002, ridgeSupport13_suffix_003, ridgeSupport13_suffix_004, ridgeSupport13_suffix_005, ridgeSupport13_suffix_006, ridgeSupport13_suffix_007, ridgeSupport13_suffix_008, ridgeSupport13_suffix_009, ridgeSupport13_suffix_010, ridgeSupport13_suffix_011, ridgeSupport13_suffix_012, ridgeSupport13_suffix_013, ridgeSupport13_suffix_014, ridgeSupport13_suffix_015, ridgeSupport13_suffix_016, ridgeSupport13_suffix_017, ridgeSupport13_suffix_018, ridgeSupport13_suffix_019, ridgeSupport13_suffix_020, ridgeSupport13_suffix_021, ridgeSupport13_suffix_022, ridgeSupport13_suffix_023, ridgeSupport13_suffix_024, ridgeSupport13_suffix_025, ridgeSupport13_suffix_026, ridgeSupport13_suffix_027, ridgeSupport13_suffix_028, ridgeSupport13_suffix_029, ridgeSupport13_suffix_030, ridgeSupport13_suffix_031, ridgeSupport13_suffix_032, ridgeSupport13_suffix_033, ridgeSupport13_suffix_034, List.all_append, List.all_nil, ridgeSupport13_000_checked, ridgeSupport13_001_checked, ridgeSupport13_002_checked, ridgeSupport13_003_checked, ridgeSupport13_004_checked, ridgeSupport13_005_checked, ridgeSupport13_006_checked, ridgeSupport13_007_checked, ridgeSupport13_008_checked, ridgeSupport13_009_checked, ridgeSupport13_010_checked, ridgeSupport13_011_checked, ridgeSupport13_012_checked, ridgeSupport13_013_checked, ridgeSupport13_014_checked, ridgeSupport13_015_checked, ridgeSupport13_016_checked, ridgeSupport13_017_checked, ridgeSupport13_018_checked, ridgeSupport13_019_checked, ridgeSupport13_020_checked, ridgeSupport13_021_checked, ridgeSupport13_022_checked, ridgeSupport13_023_checked, ridgeSupport13_024_checked, ridgeSupport13_025_checked, ridgeSupport13_026_checked, ridgeSupport13_027_checked, ridgeSupport13_028_checked, ridgeSupport13_029_checked, ridgeSupport13_030_checked, ridgeSupport13_031_checked, ridgeSupport13_032_checked, ridgeSupport13_033_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
