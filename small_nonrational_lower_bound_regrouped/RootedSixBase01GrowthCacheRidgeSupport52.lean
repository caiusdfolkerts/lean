module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport52Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 52 034 14
cert_ridgeSupport_suffix_decode_2 52 033 14 5 5 034 034 0
cert_ridgeSupport_suffix_decode_2 52 032 14 37 32 034 033 5
cert_ridgeSupport_suffix_decode_2 52 031 14 69 32 034 032 37
cert_ridgeSupport_suffix_decode_2 52 030 14 101 32 034 031 69
cert_ridgeSupport_suffix_decode_2 52 029 14 133 32 034 030 101
cert_ridgeSupport_suffix_decode_2 52 028 14 165 32 034 029 133
cert_ridgeSupport_suffix_decode_2 52 027 14 197 32 034 028 165
cert_ridgeSupport_suffix_decode_2 52 026 14 229 32 034 027 197
cert_ridgeSupport_suffix_decode_2 52 025 14 261 32 034 026 229
cert_ridgeSupport_suffix_decode_2 52 024 14 293 32 034 025 261
cert_ridgeSupport_suffix_decode_2 52 023 14 325 32 034 024 293
cert_ridgeSupport_suffix_decode_2 52 022 14 357 32 034 023 325
cert_ridgeSupport_suffix_decode_2 52 021 14 389 32 034 022 357
cert_ridgeSupport_suffix_decode_2 52 020 14 421 32 034 021 389
cert_ridgeSupport_suffix_decode_2 52 019 14 453 32 034 020 421
cert_ridgeSupport_suffix_decode_2 52 018 14 485 32 034 019 453
cert_ridgeSupport_suffix_decode_2 52 017 14 517 32 034 018 485
cert_ridgeSupport_suffix_decode_2 52 016 14 549 32 034 017 517
cert_ridgeSupport_suffix_decode_2 52 015 14 581 32 034 016 549
cert_ridgeSupport_suffix_decode_2 52 014 14 613 32 034 015 581
cert_ridgeSupport_suffix_decode_2 52 013 14 645 32 034 014 613
cert_ridgeSupport_suffix_decode_2 52 012 14 677 32 034 013 645
cert_ridgeSupport_suffix_decode_2 52 011 14 709 32 034 012 677
cert_ridgeSupport_suffix_decode_2 52 010 14 741 32 034 011 709
cert_ridgeSupport_suffix_decode_2 52 009 14 773 32 034 010 741
cert_ridgeSupport_suffix_decode_2 52 008 14 805 32 034 009 773
cert_ridgeSupport_suffix_decode_2 52 007 14 837 32 034 008 805
cert_ridgeSupport_suffix_decode_2 52 006 14 869 32 034 007 837
cert_ridgeSupport_suffix_decode_2 52 005 14 901 32 034 006 869
cert_ridgeSupport_suffix_decode_2 52 004 14 933 32 034 005 901
cert_ridgeSupport_suffix_decode_2 52 003 14 965 32 034 004 933
cert_ridgeSupport_suffix_decode_2 52 002 14 997 32 034 003 965
cert_ridgeSupport_suffix_decode_2 52 001 14 1029 32 034 002 997
cert_ridgeSupport_suffix_decode_2 52 000 14 1061 32 034 001 1029
cert_ridgeSupport_eq_3 52
theorem ridgeTest_large_52 : ridgeTest 52 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, ridgeSupport52_suffix_012, ridgeSupport52_suffix_013, ridgeSupport52_suffix_014, ridgeSupport52_suffix_015, ridgeSupport52_suffix_016, ridgeSupport52_suffix_017, ridgeSupport52_suffix_018, ridgeSupport52_suffix_019, ridgeSupport52_suffix_020, ridgeSupport52_suffix_021, ridgeSupport52_suffix_022, ridgeSupport52_suffix_023, ridgeSupport52_suffix_024, ridgeSupport52_suffix_025, ridgeSupport52_suffix_026, ridgeSupport52_suffix_027, ridgeSupport52_suffix_028, ridgeSupport52_suffix_029, ridgeSupport52_suffix_030, ridgeSupport52_suffix_031, ridgeSupport52_suffix_032, ridgeSupport52_suffix_033, ridgeSupport52_suffix_034, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport52_000_mask, ridgeSupport52_001_mask, ridgeSupport52_002_mask, ridgeSupport52_003_mask, ridgeSupport52_004_mask, ridgeSupport52_005_mask, ridgeSupport52_006_mask, ridgeSupport52_007_mask, ridgeSupport52_008_mask, ridgeSupport52_009_mask, ridgeSupport52_010_mask, ridgeSupport52_011_mask, ridgeSupport52_012_mask, ridgeSupport52_013_mask, ridgeSupport52_014_mask, ridgeSupport52_015_mask, ridgeSupport52_016_mask, ridgeSupport52_017_mask, ridgeSupport52_018_mask, ridgeSupport52_019_mask, ridgeSupport52_020_mask, ridgeSupport52_021_mask, ridgeSupport52_022_mask, ridgeSupport52_023_mask, ridgeSupport52_024_mask, ridgeSupport52_025_mask, ridgeSupport52_026_mask, ridgeSupport52_027_mask, ridgeSupport52_028_mask, ridgeSupport52_029_mask, ridgeSupport52_030_mask, ridgeSupport52_031_mask, ridgeSupport52_032_mask, ridgeSupport52_033_mask]
    decide +kernel
  · rw [ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, ridgeSupport52_suffix_012, ridgeSupport52_suffix_013, ridgeSupport52_suffix_014, ridgeSupport52_suffix_015, ridgeSupport52_suffix_016, ridgeSupport52_suffix_017, ridgeSupport52_suffix_018, ridgeSupport52_suffix_019, ridgeSupport52_suffix_020, ridgeSupport52_suffix_021, ridgeSupport52_suffix_022, ridgeSupport52_suffix_023, ridgeSupport52_suffix_024, ridgeSupport52_suffix_025, ridgeSupport52_suffix_026, ridgeSupport52_suffix_027, ridgeSupport52_suffix_028, ridgeSupport52_suffix_029, ridgeSupport52_suffix_030, ridgeSupport52_suffix_031, ridgeSupport52_suffix_032, ridgeSupport52_suffix_033, ridgeSupport52_suffix_034, List.all_append, List.all_nil, ridgeSupport52_000_checked, ridgeSupport52_001_checked, ridgeSupport52_002_checked, ridgeSupport52_003_checked, ridgeSupport52_004_checked, ridgeSupport52_005_checked, ridgeSupport52_006_checked, ridgeSupport52_007_checked, ridgeSupport52_008_checked, ridgeSupport52_009_checked, ridgeSupport52_010_checked, ridgeSupport52_011_checked, ridgeSupport52_012_checked, ridgeSupport52_013_checked, ridgeSupport52_014_checked, ridgeSupport52_015_checked, ridgeSupport52_016_checked, ridgeSupport52_017_checked, ridgeSupport52_018_checked, ridgeSupport52_019_checked, ridgeSupport52_020_checked, ridgeSupport52_021_checked, ridgeSupport52_022_checked, ridgeSupport52_023_checked, ridgeSupport52_024_checked, ridgeSupport52_025_checked, ridgeSupport52_026_checked, ridgeSupport52_027_checked, ridgeSupport52_028_checked, ridgeSupport52_029_checked, ridgeSupport52_030_checked, ridgeSupport52_031_checked, ridgeSupport52_032_checked, ridgeSupport52_033_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
