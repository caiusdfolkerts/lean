module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport960Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 960 034 14
cert_ridgeSupport_suffix_decode_2 960 033 14 18 18 034 034 0
cert_ridgeSupport_suffix_decode_2 960 032 14 50 32 034 033 18
cert_ridgeSupport_suffix_decode_2 960 031 14 82 32 034 032 50
cert_ridgeSupport_suffix_decode_2 960 030 14 114 32 034 031 82
cert_ridgeSupport_suffix_decode_2 960 029 14 146 32 034 030 114
cert_ridgeSupport_suffix_decode_2 960 028 14 178 32 034 029 146
cert_ridgeSupport_suffix_decode_2 960 027 14 210 32 034 028 178
cert_ridgeSupport_suffix_decode_2 960 026 14 242 32 034 027 210
cert_ridgeSupport_suffix_decode_2 960 025 14 274 32 034 026 242
cert_ridgeSupport_suffix_decode_2 960 024 14 306 32 034 025 274
cert_ridgeSupport_suffix_decode_2 960 023 14 338 32 034 024 306
cert_ridgeSupport_suffix_decode_2 960 022 14 370 32 034 023 338
cert_ridgeSupport_suffix_decode_2 960 021 14 402 32 034 022 370
cert_ridgeSupport_suffix_decode_2 960 020 14 434 32 034 021 402
cert_ridgeSupport_suffix_decode_2 960 019 14 466 32 034 020 434
cert_ridgeSupport_suffix_decode_2 960 018 14 498 32 034 019 466
cert_ridgeSupport_suffix_decode_2 960 017 14 530 32 034 018 498
cert_ridgeSupport_suffix_decode_2 960 016 14 562 32 034 017 530
cert_ridgeSupport_suffix_decode_2 960 015 14 594 32 034 016 562
cert_ridgeSupport_suffix_decode_2 960 014 14 626 32 034 015 594
cert_ridgeSupport_suffix_decode_2 960 013 14 658 32 034 014 626
cert_ridgeSupport_suffix_decode_2 960 012 14 690 32 034 013 658
cert_ridgeSupport_suffix_decode_2 960 011 14 722 32 034 012 690
cert_ridgeSupport_suffix_decode_2 960 010 14 754 32 034 011 722
cert_ridgeSupport_suffix_decode_2 960 009 14 786 32 034 010 754
cert_ridgeSupport_suffix_decode_2 960 008 14 818 32 034 009 786
cert_ridgeSupport_suffix_decode_2 960 007 14 850 32 034 008 818
cert_ridgeSupport_suffix_decode_2 960 006 14 882 32 034 007 850
cert_ridgeSupport_suffix_decode_2 960 005 14 914 32 034 006 882
cert_ridgeSupport_suffix_decode_2 960 004 14 946 32 034 005 914
cert_ridgeSupport_suffix_decode_2 960 003 14 978 32 034 004 946
cert_ridgeSupport_suffix_decode_2 960 002 14 1010 32 034 003 978
cert_ridgeSupport_suffix_decode_2 960 001 14 1042 32 034 002 1010
cert_ridgeSupport_suffix_decode_2 960 000 14 1074 32 034 001 1042
cert_ridgeSupport_eq_3 960
theorem ridgeTest_large_960 : ridgeTest 960 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, ridgeSupport960_suffix_021, ridgeSupport960_suffix_022, ridgeSupport960_suffix_023, ridgeSupport960_suffix_024, ridgeSupport960_suffix_025, ridgeSupport960_suffix_026, ridgeSupport960_suffix_027, ridgeSupport960_suffix_028, ridgeSupport960_suffix_029, ridgeSupport960_suffix_030, ridgeSupport960_suffix_031, ridgeSupport960_suffix_032, ridgeSupport960_suffix_033, ridgeSupport960_suffix_034, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport960_000_mask, ridgeSupport960_001_mask, ridgeSupport960_002_mask, ridgeSupport960_003_mask, ridgeSupport960_004_mask, ridgeSupport960_005_mask, ridgeSupport960_006_mask, ridgeSupport960_007_mask, ridgeSupport960_008_mask, ridgeSupport960_009_mask, ridgeSupport960_010_mask, ridgeSupport960_011_mask, ridgeSupport960_012_mask, ridgeSupport960_013_mask, ridgeSupport960_014_mask, ridgeSupport960_015_mask, ridgeSupport960_016_mask, ridgeSupport960_017_mask, ridgeSupport960_018_mask, ridgeSupport960_019_mask, ridgeSupport960_020_mask, ridgeSupport960_021_mask, ridgeSupport960_022_mask, ridgeSupport960_023_mask, ridgeSupport960_024_mask, ridgeSupport960_025_mask, ridgeSupport960_026_mask, ridgeSupport960_027_mask, ridgeSupport960_028_mask, ridgeSupport960_029_mask, ridgeSupport960_030_mask, ridgeSupport960_031_mask, ridgeSupport960_032_mask, ridgeSupport960_033_mask]
    decide +kernel
  · rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, ridgeSupport960_suffix_021, ridgeSupport960_suffix_022, ridgeSupport960_suffix_023, ridgeSupport960_suffix_024, ridgeSupport960_suffix_025, ridgeSupport960_suffix_026, ridgeSupport960_suffix_027, ridgeSupport960_suffix_028, ridgeSupport960_suffix_029, ridgeSupport960_suffix_030, ridgeSupport960_suffix_031, ridgeSupport960_suffix_032, ridgeSupport960_suffix_033, ridgeSupport960_suffix_034, List.all_append, List.all_nil, ridgeSupport960_000_checked, ridgeSupport960_001_checked, ridgeSupport960_002_checked, ridgeSupport960_003_checked, ridgeSupport960_004_checked, ridgeSupport960_005_checked, ridgeSupport960_006_checked, ridgeSupport960_007_checked, ridgeSupport960_008_checked, ridgeSupport960_009_checked, ridgeSupport960_010_checked, ridgeSupport960_011_checked, ridgeSupport960_012_checked, ridgeSupport960_013_checked, ridgeSupport960_014_checked, ridgeSupport960_015_checked, ridgeSupport960_016_checked, ridgeSupport960_017_checked, ridgeSupport960_018_checked, ridgeSupport960_019_checked, ridgeSupport960_020_checked, ridgeSupport960_021_checked, ridgeSupport960_022_checked, ridgeSupport960_023_checked, ridgeSupport960_024_checked, ridgeSupport960_025_checked, ridgeSupport960_026_checked, ridgeSupport960_027_checked, ridgeSupport960_028_checked, ridgeSupport960_029_checked, ridgeSupport960_030_checked, ridgeSupport960_031_checked, ridgeSupport960_032_checked, ridgeSupport960_033_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
