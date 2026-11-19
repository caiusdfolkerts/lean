module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport960Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 960 037 15
cert_ridgeSupport_suffix_decode_2 960 036 15 18 18 037 037 0
cert_ridgeSupport_suffix_decode_2 960 035 15 50 32 037 036 18
cert_ridgeSupport_suffix_decode_2 960 034 15 82 32 037 035 50
cert_ridgeSupport_suffix_decode_2 960 033 15 114 32 037 034 82
cert_ridgeSupport_suffix_decode_2 960 032 15 146 32 037 033 114
cert_ridgeSupport_suffix_decode_2 960 031 15 178 32 037 032 146
cert_ridgeSupport_suffix_decode_2 960 030 15 210 32 037 031 178
cert_ridgeSupport_suffix_decode_2 960 029 15 242 32 037 030 210
cert_ridgeSupport_suffix_decode_2 960 028 15 274 32 037 029 242
cert_ridgeSupport_suffix_decode_2 960 027 15 306 32 037 028 274
cert_ridgeSupport_suffix_decode_2 960 026 15 338 32 037 027 306
cert_ridgeSupport_suffix_decode_2 960 025 15 370 32 037 026 338
cert_ridgeSupport_suffix_decode_2 960 024 15 402 32 037 025 370
cert_ridgeSupport_suffix_decode_2 960 023 15 434 32 037 024 402
cert_ridgeSupport_suffix_decode_2 960 022 15 466 32 037 023 434
cert_ridgeSupport_suffix_decode_2 960 021 15 498 32 037 022 466
cert_ridgeSupport_suffix_decode_2 960 020 15 530 32 037 021 498
cert_ridgeSupport_suffix_decode_2 960 019 15 562 32 037 020 530
cert_ridgeSupport_suffix_decode_2 960 018 15 594 32 037 019 562
cert_ridgeSupport_suffix_decode_2 960 017 15 626 32 037 018 594
cert_ridgeSupport_suffix_decode_2 960 016 15 658 32 037 017 626
cert_ridgeSupport_suffix_decode_2 960 015 15 690 32 037 016 658
cert_ridgeSupport_suffix_decode_2 960 014 15 722 32 037 015 690
cert_ridgeSupport_suffix_decode_2 960 013 15 754 32 037 014 722
cert_ridgeSupport_suffix_decode_2 960 012 15 786 32 037 013 754
cert_ridgeSupport_suffix_decode_2 960 011 15 818 32 037 012 786
cert_ridgeSupport_suffix_decode_2 960 010 15 850 32 037 011 818
cert_ridgeSupport_suffix_decode_2 960 009 15 882 32 037 010 850
cert_ridgeSupport_suffix_decode_2 960 008 15 914 32 037 009 882
cert_ridgeSupport_suffix_decode_2 960 007 15 946 32 037 008 914
cert_ridgeSupport_suffix_decode_2 960 006 15 978 32 037 007 946
cert_ridgeSupport_suffix_decode_2 960 005 15 1010 32 037 006 978
cert_ridgeSupport_suffix_decode_2 960 004 15 1042 32 037 005 1010
cert_ridgeSupport_suffix_decode_2 960 003 15 1074 32 037 004 1042
cert_ridgeSupport_suffix_decode_2 960 002 15 1106 32 037 003 1074
cert_ridgeSupport_suffix_decode_2 960 001 15 1138 32 037 002 1106
cert_ridgeSupport_suffix_decode_2 960 000 15 1170 32 037 001 1138
cert_ridgeSupport_eq_3 960
theorem ridgeTest_large_960 : ridgeTest 960 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, ridgeSupport960_suffix_021, ridgeSupport960_suffix_022, ridgeSupport960_suffix_023, ridgeSupport960_suffix_024, ridgeSupport960_suffix_025, ridgeSupport960_suffix_026, ridgeSupport960_suffix_027, ridgeSupport960_suffix_028, ridgeSupport960_suffix_029, ridgeSupport960_suffix_030, ridgeSupport960_suffix_031, ridgeSupport960_suffix_032, ridgeSupport960_suffix_033, ridgeSupport960_suffix_034, ridgeSupport960_suffix_035, ridgeSupport960_suffix_036, ridgeSupport960_suffix_037, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport960_000_mask, ridgeSupport960_001_mask, ridgeSupport960_002_mask, ridgeSupport960_003_mask, ridgeSupport960_004_mask, ridgeSupport960_005_mask, ridgeSupport960_006_mask, ridgeSupport960_007_mask, ridgeSupport960_008_mask, ridgeSupport960_009_mask, ridgeSupport960_010_mask, ridgeSupport960_011_mask, ridgeSupport960_012_mask, ridgeSupport960_013_mask, ridgeSupport960_014_mask, ridgeSupport960_015_mask, ridgeSupport960_016_mask, ridgeSupport960_017_mask, ridgeSupport960_018_mask, ridgeSupport960_019_mask, ridgeSupport960_020_mask, ridgeSupport960_021_mask, ridgeSupport960_022_mask, ridgeSupport960_023_mask, ridgeSupport960_024_mask, ridgeSupport960_025_mask, ridgeSupport960_026_mask, ridgeSupport960_027_mask, ridgeSupport960_028_mask, ridgeSupport960_029_mask, ridgeSupport960_030_mask, ridgeSupport960_031_mask, ridgeSupport960_032_mask, ridgeSupport960_033_mask, ridgeSupport960_034_mask, ridgeSupport960_035_mask, ridgeSupport960_036_mask]
    decide +kernel
  · rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, ridgeSupport960_suffix_021, ridgeSupport960_suffix_022, ridgeSupport960_suffix_023, ridgeSupport960_suffix_024, ridgeSupport960_suffix_025, ridgeSupport960_suffix_026, ridgeSupport960_suffix_027, ridgeSupport960_suffix_028, ridgeSupport960_suffix_029, ridgeSupport960_suffix_030, ridgeSupport960_suffix_031, ridgeSupport960_suffix_032, ridgeSupport960_suffix_033, ridgeSupport960_suffix_034, ridgeSupport960_suffix_035, ridgeSupport960_suffix_036, ridgeSupport960_suffix_037, List.all_append, List.all_nil, ridgeSupport960_000_checked, ridgeSupport960_001_checked, ridgeSupport960_002_checked, ridgeSupport960_003_checked, ridgeSupport960_004_checked, ridgeSupport960_005_checked, ridgeSupport960_006_checked, ridgeSupport960_007_checked, ridgeSupport960_008_checked, ridgeSupport960_009_checked, ridgeSupport960_010_checked, ridgeSupport960_011_checked, ridgeSupport960_012_checked, ridgeSupport960_013_checked, ridgeSupport960_014_checked, ridgeSupport960_015_checked, ridgeSupport960_016_checked, ridgeSupport960_017_checked, ridgeSupport960_018_checked, ridgeSupport960_019_checked, ridgeSupport960_020_checked, ridgeSupport960_021_checked, ridgeSupport960_022_checked, ridgeSupport960_023_checked, ridgeSupport960_024_checked, ridgeSupport960_025_checked, ridgeSupport960_026_checked, ridgeSupport960_027_checked, ridgeSupport960_028_checked, ridgeSupport960_029_checked, ridgeSupport960_030_checked, ridgeSupport960_031_checked, ridgeSupport960_032_checked, ridgeSupport960_033_checked, ridgeSupport960_034_checked, ridgeSupport960_035_checked, ridgeSupport960_036_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
