module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport7Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 7 034 14
cert_ridgeSupport_suffix_decode_2 7 033 14 5 5 034 034 0
cert_ridgeSupport_suffix_decode_2 7 032 14 37 32 034 033 5
cert_ridgeSupport_suffix_decode_2 7 031 14 69 32 034 032 37
cert_ridgeSupport_suffix_decode_2 7 030 14 101 32 034 031 69
cert_ridgeSupport_suffix_decode_2 7 029 14 133 32 034 030 101
cert_ridgeSupport_suffix_decode_2 7 028 14 165 32 034 029 133
cert_ridgeSupport_suffix_decode_2 7 027 14 197 32 034 028 165
cert_ridgeSupport_suffix_decode_2 7 026 14 229 32 034 027 197
cert_ridgeSupport_suffix_decode_2 7 025 14 261 32 034 026 229
cert_ridgeSupport_suffix_decode_2 7 024 14 293 32 034 025 261
cert_ridgeSupport_suffix_decode_2 7 023 14 325 32 034 024 293
cert_ridgeSupport_suffix_decode_2 7 022 14 357 32 034 023 325
cert_ridgeSupport_suffix_decode_2 7 021 14 389 32 034 022 357
cert_ridgeSupport_suffix_decode_2 7 020 14 421 32 034 021 389
cert_ridgeSupport_suffix_decode_2 7 019 14 453 32 034 020 421
cert_ridgeSupport_suffix_decode_2 7 018 14 485 32 034 019 453
cert_ridgeSupport_suffix_decode_2 7 017 14 517 32 034 018 485
cert_ridgeSupport_suffix_decode_2 7 016 14 549 32 034 017 517
cert_ridgeSupport_suffix_decode_2 7 015 14 581 32 034 016 549
cert_ridgeSupport_suffix_decode_2 7 014 14 613 32 034 015 581
cert_ridgeSupport_suffix_decode_2 7 013 14 645 32 034 014 613
cert_ridgeSupport_suffix_decode_2 7 012 14 677 32 034 013 645
cert_ridgeSupport_suffix_decode_2 7 011 14 709 32 034 012 677
cert_ridgeSupport_suffix_decode_2 7 010 14 741 32 034 011 709
cert_ridgeSupport_suffix_decode_2 7 009 14 773 32 034 010 741
cert_ridgeSupport_suffix_decode_2 7 008 14 805 32 034 009 773
cert_ridgeSupport_suffix_decode_2 7 007 14 837 32 034 008 805
cert_ridgeSupport_suffix_decode_2 7 006 14 869 32 034 007 837
cert_ridgeSupport_suffix_decode_2 7 005 14 901 32 034 006 869
cert_ridgeSupport_suffix_decode_2 7 004 14 933 32 034 005 901
cert_ridgeSupport_suffix_decode_2 7 003 14 965 32 034 004 933
cert_ridgeSupport_suffix_decode_2 7 002 14 997 32 034 003 965
cert_ridgeSupport_suffix_decode_2 7 001 14 1029 32 034 002 997
cert_ridgeSupport_suffix_decode_2 7 000 14 1061 32 034 001 1029
cert_ridgeSupport_eq_3 7
theorem ridgeTest_large_7 : ridgeTest 7 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, ridgeSupport7_suffix_016, ridgeSupport7_suffix_017, ridgeSupport7_suffix_018, ridgeSupport7_suffix_019, ridgeSupport7_suffix_020, ridgeSupport7_suffix_021, ridgeSupport7_suffix_022, ridgeSupport7_suffix_023, ridgeSupport7_suffix_024, ridgeSupport7_suffix_025, ridgeSupport7_suffix_026, ridgeSupport7_suffix_027, ridgeSupport7_suffix_028, ridgeSupport7_suffix_029, ridgeSupport7_suffix_030, ridgeSupport7_suffix_031, ridgeSupport7_suffix_032, ridgeSupport7_suffix_033, ridgeSupport7_suffix_034, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport7_000_mask, ridgeSupport7_001_mask, ridgeSupport7_002_mask, ridgeSupport7_003_mask, ridgeSupport7_004_mask, ridgeSupport7_005_mask, ridgeSupport7_006_mask, ridgeSupport7_007_mask, ridgeSupport7_008_mask, ridgeSupport7_009_mask, ridgeSupport7_010_mask, ridgeSupport7_011_mask, ridgeSupport7_012_mask, ridgeSupport7_013_mask, ridgeSupport7_014_mask, ridgeSupport7_015_mask, ridgeSupport7_016_mask, ridgeSupport7_017_mask, ridgeSupport7_018_mask, ridgeSupport7_019_mask, ridgeSupport7_020_mask, ridgeSupport7_021_mask, ridgeSupport7_022_mask, ridgeSupport7_023_mask, ridgeSupport7_024_mask, ridgeSupport7_025_mask, ridgeSupport7_026_mask, ridgeSupport7_027_mask, ridgeSupport7_028_mask, ridgeSupport7_029_mask, ridgeSupport7_030_mask, ridgeSupport7_031_mask, ridgeSupport7_032_mask, ridgeSupport7_033_mask]
    decide +kernel
  · rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, ridgeSupport7_suffix_016, ridgeSupport7_suffix_017, ridgeSupport7_suffix_018, ridgeSupport7_suffix_019, ridgeSupport7_suffix_020, ridgeSupport7_suffix_021, ridgeSupport7_suffix_022, ridgeSupport7_suffix_023, ridgeSupport7_suffix_024, ridgeSupport7_suffix_025, ridgeSupport7_suffix_026, ridgeSupport7_suffix_027, ridgeSupport7_suffix_028, ridgeSupport7_suffix_029, ridgeSupport7_suffix_030, ridgeSupport7_suffix_031, ridgeSupport7_suffix_032, ridgeSupport7_suffix_033, ridgeSupport7_suffix_034, List.all_append, List.all_nil, ridgeSupport7_000_checked, ridgeSupport7_001_checked, ridgeSupport7_002_checked, ridgeSupport7_003_checked, ridgeSupport7_004_checked, ridgeSupport7_005_checked, ridgeSupport7_006_checked, ridgeSupport7_007_checked, ridgeSupport7_008_checked, ridgeSupport7_009_checked, ridgeSupport7_010_checked, ridgeSupport7_011_checked, ridgeSupport7_012_checked, ridgeSupport7_013_checked, ridgeSupport7_014_checked, ridgeSupport7_015_checked, ridgeSupport7_016_checked, ridgeSupport7_017_checked, ridgeSupport7_018_checked, ridgeSupport7_019_checked, ridgeSupport7_020_checked, ridgeSupport7_021_checked, ridgeSupport7_022_checked, ridgeSupport7_023_checked, ridgeSupport7_024_checked, ridgeSupport7_025_checked, ridgeSupport7_026_checked, ridgeSupport7_027_checked, ridgeSupport7_028_checked, ridgeSupport7_029_checked, ridgeSupport7_030_checked, ridgeSupport7_031_checked, ridgeSupport7_032_checked, ridgeSupport7_033_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
