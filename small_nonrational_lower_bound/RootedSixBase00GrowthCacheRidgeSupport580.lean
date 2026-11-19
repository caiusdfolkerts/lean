module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport580Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 580 060 15
cert_ridgeSupport_suffix_decode_2 580 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 580 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 580 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 580 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 580 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 580 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 580 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 580 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 580 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 580 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 580 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 580 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 580 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 580 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 580 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 580 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 580 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 580 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 580 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 580 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 580 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 580 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 580 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 580 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 580 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 580 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 580 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 580 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 580 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 580 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 580 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 580 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 580 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 580 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 580 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 580 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 580 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 580 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 580 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 580 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 580 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 580 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 580 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 580 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 580 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 580 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 580 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 580 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 580 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 580 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 580 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 580 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 580 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 580 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 580 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 580 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 580 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 580 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 580 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 580 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 580
theorem ridgeTest_large_580 : ridgeTest 580 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, ridgeSupport580_suffix_010, ridgeSupport580_suffix_011, ridgeSupport580_suffix_012, ridgeSupport580_suffix_013, ridgeSupport580_suffix_014, ridgeSupport580_suffix_015, ridgeSupport580_suffix_016, ridgeSupport580_suffix_017, ridgeSupport580_suffix_018, ridgeSupport580_suffix_019, ridgeSupport580_suffix_020, ridgeSupport580_suffix_021, ridgeSupport580_suffix_022, ridgeSupport580_suffix_023, ridgeSupport580_suffix_024, ridgeSupport580_suffix_025, ridgeSupport580_suffix_026, ridgeSupport580_suffix_027, ridgeSupport580_suffix_028, ridgeSupport580_suffix_029, ridgeSupport580_suffix_030, ridgeSupport580_suffix_031, ridgeSupport580_suffix_032, ridgeSupport580_suffix_033, ridgeSupport580_suffix_034, ridgeSupport580_suffix_035, ridgeSupport580_suffix_036, ridgeSupport580_suffix_037, ridgeSupport580_suffix_038, ridgeSupport580_suffix_039, ridgeSupport580_suffix_040, ridgeSupport580_suffix_041, ridgeSupport580_suffix_042, ridgeSupport580_suffix_043, ridgeSupport580_suffix_044, ridgeSupport580_suffix_045, ridgeSupport580_suffix_046, ridgeSupport580_suffix_047, ridgeSupport580_suffix_048, ridgeSupport580_suffix_049, ridgeSupport580_suffix_050, ridgeSupport580_suffix_051, ridgeSupport580_suffix_052, ridgeSupport580_suffix_053, ridgeSupport580_suffix_054, ridgeSupport580_suffix_055, ridgeSupport580_suffix_056, ridgeSupport580_suffix_057, ridgeSupport580_suffix_058, ridgeSupport580_suffix_059, ridgeSupport580_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport580_000_mask, ridgeSupport580_001_mask, ridgeSupport580_002_mask, ridgeSupport580_003_mask, ridgeSupport580_004_mask, ridgeSupport580_005_mask, ridgeSupport580_006_mask, ridgeSupport580_007_mask, ridgeSupport580_008_mask, ridgeSupport580_009_mask, ridgeSupport580_010_mask, ridgeSupport580_011_mask, ridgeSupport580_012_mask, ridgeSupport580_013_mask, ridgeSupport580_014_mask, ridgeSupport580_015_mask, ridgeSupport580_016_mask, ridgeSupport580_017_mask, ridgeSupport580_018_mask, ridgeSupport580_019_mask, ridgeSupport580_020_mask, ridgeSupport580_021_mask, ridgeSupport580_022_mask, ridgeSupport580_023_mask, ridgeSupport580_024_mask, ridgeSupport580_025_mask, ridgeSupport580_026_mask, ridgeSupport580_027_mask, ridgeSupport580_028_mask, ridgeSupport580_029_mask, ridgeSupport580_030_mask, ridgeSupport580_031_mask, ridgeSupport580_032_mask, ridgeSupport580_033_mask, ridgeSupport580_034_mask, ridgeSupport580_035_mask, ridgeSupport580_036_mask, ridgeSupport580_037_mask, ridgeSupport580_038_mask, ridgeSupport580_039_mask, ridgeSupport580_040_mask, ridgeSupport580_041_mask, ridgeSupport580_042_mask, ridgeSupport580_043_mask, ridgeSupport580_044_mask, ridgeSupport580_045_mask, ridgeSupport580_046_mask, ridgeSupport580_047_mask, ridgeSupport580_048_mask, ridgeSupport580_049_mask, ridgeSupport580_050_mask, ridgeSupport580_051_mask, ridgeSupport580_052_mask, ridgeSupport580_053_mask, ridgeSupport580_054_mask, ridgeSupport580_055_mask, ridgeSupport580_056_mask, ridgeSupport580_057_mask, ridgeSupport580_058_mask, ridgeSupport580_059_mask]
    decide +kernel
  · rw [ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, ridgeSupport580_suffix_010, ridgeSupport580_suffix_011, ridgeSupport580_suffix_012, ridgeSupport580_suffix_013, ridgeSupport580_suffix_014, ridgeSupport580_suffix_015, ridgeSupport580_suffix_016, ridgeSupport580_suffix_017, ridgeSupport580_suffix_018, ridgeSupport580_suffix_019, ridgeSupport580_suffix_020, ridgeSupport580_suffix_021, ridgeSupport580_suffix_022, ridgeSupport580_suffix_023, ridgeSupport580_suffix_024, ridgeSupport580_suffix_025, ridgeSupport580_suffix_026, ridgeSupport580_suffix_027, ridgeSupport580_suffix_028, ridgeSupport580_suffix_029, ridgeSupport580_suffix_030, ridgeSupport580_suffix_031, ridgeSupport580_suffix_032, ridgeSupport580_suffix_033, ridgeSupport580_suffix_034, ridgeSupport580_suffix_035, ridgeSupport580_suffix_036, ridgeSupport580_suffix_037, ridgeSupport580_suffix_038, ridgeSupport580_suffix_039, ridgeSupport580_suffix_040, ridgeSupport580_suffix_041, ridgeSupport580_suffix_042, ridgeSupport580_suffix_043, ridgeSupport580_suffix_044, ridgeSupport580_suffix_045, ridgeSupport580_suffix_046, ridgeSupport580_suffix_047, ridgeSupport580_suffix_048, ridgeSupport580_suffix_049, ridgeSupport580_suffix_050, ridgeSupport580_suffix_051, ridgeSupport580_suffix_052, ridgeSupport580_suffix_053, ridgeSupport580_suffix_054, ridgeSupport580_suffix_055, ridgeSupport580_suffix_056, ridgeSupport580_suffix_057, ridgeSupport580_suffix_058, ridgeSupport580_suffix_059, ridgeSupport580_suffix_060, List.all_append, List.all_nil, ridgeSupport580_000_checked, ridgeSupport580_001_checked, ridgeSupport580_002_checked, ridgeSupport580_003_checked, ridgeSupport580_004_checked, ridgeSupport580_005_checked, ridgeSupport580_006_checked, ridgeSupport580_007_checked, ridgeSupport580_008_checked, ridgeSupport580_009_checked, ridgeSupport580_010_checked, ridgeSupport580_011_checked, ridgeSupport580_012_checked, ridgeSupport580_013_checked, ridgeSupport580_014_checked, ridgeSupport580_015_checked, ridgeSupport580_016_checked, ridgeSupport580_017_checked, ridgeSupport580_018_checked, ridgeSupport580_019_checked, ridgeSupport580_020_checked, ridgeSupport580_021_checked, ridgeSupport580_022_checked, ridgeSupport580_023_checked, ridgeSupport580_024_checked, ridgeSupport580_025_checked, ridgeSupport580_026_checked, ridgeSupport580_027_checked, ridgeSupport580_028_checked, ridgeSupport580_029_checked, ridgeSupport580_030_checked, ridgeSupport580_031_checked, ridgeSupport580_032_checked, ridgeSupport580_033_checked, ridgeSupport580_034_checked, ridgeSupport580_035_checked, ridgeSupport580_036_checked, ridgeSupport580_037_checked, ridgeSupport580_038_checked, ridgeSupport580_039_checked, ridgeSupport580_040_checked, ridgeSupport580_041_checked, ridgeSupport580_042_checked, ridgeSupport580_043_checked, ridgeSupport580_044_checked, ridgeSupport580_045_checked, ridgeSupport580_046_checked, ridgeSupport580_047_checked, ridgeSupport580_048_checked, ridgeSupport580_049_checked, ridgeSupport580_050_checked, ridgeSupport580_051_checked, ridgeSupport580_052_checked, ridgeSupport580_053_checked, ridgeSupport580_054_checked, ridgeSupport580_055_checked, ridgeSupport580_056_checked, ridgeSupport580_057_checked, ridgeSupport580_058_checked, ridgeSupport580_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
