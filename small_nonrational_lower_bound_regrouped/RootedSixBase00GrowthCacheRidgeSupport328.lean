module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport328Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 328 060 15
cert_ridgeSupport_suffix_decode_2 328 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 328 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 328 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 328 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 328 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 328 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 328 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 328 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 328 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 328 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 328 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 328 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 328 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 328 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 328 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 328 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 328 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 328 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 328 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 328 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 328 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 328 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 328 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 328 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 328 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 328 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 328 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 328 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 328 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 328 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 328 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 328 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 328 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 328 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 328 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 328 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 328 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 328 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 328 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 328 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 328 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 328 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 328 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 328 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 328 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 328 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 328 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 328 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 328 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 328 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 328 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 328 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 328 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 328 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 328 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 328 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 328 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 328 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 328 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 328 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 328
theorem ridgeTest_large_328 : ridgeTest 328 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport328_eq]
    simp only [ridgeSupport328_suffix_000, ridgeSupport328_suffix_001, ridgeSupport328_suffix_002, ridgeSupport328_suffix_003, ridgeSupport328_suffix_004, ridgeSupport328_suffix_005, ridgeSupport328_suffix_006, ridgeSupport328_suffix_007, ridgeSupport328_suffix_008, ridgeSupport328_suffix_009, ridgeSupport328_suffix_010, ridgeSupport328_suffix_011, ridgeSupport328_suffix_012, ridgeSupport328_suffix_013, ridgeSupport328_suffix_014, ridgeSupport328_suffix_015, ridgeSupport328_suffix_016, ridgeSupport328_suffix_017, ridgeSupport328_suffix_018, ridgeSupport328_suffix_019, ridgeSupport328_suffix_020, ridgeSupport328_suffix_021, ridgeSupport328_suffix_022, ridgeSupport328_suffix_023, ridgeSupport328_suffix_024, ridgeSupport328_suffix_025, ridgeSupport328_suffix_026, ridgeSupport328_suffix_027, ridgeSupport328_suffix_028, ridgeSupport328_suffix_029, ridgeSupport328_suffix_030, ridgeSupport328_suffix_031, ridgeSupport328_suffix_032, ridgeSupport328_suffix_033, ridgeSupport328_suffix_034, ridgeSupport328_suffix_035, ridgeSupport328_suffix_036, ridgeSupport328_suffix_037, ridgeSupport328_suffix_038, ridgeSupport328_suffix_039, ridgeSupport328_suffix_040, ridgeSupport328_suffix_041, ridgeSupport328_suffix_042, ridgeSupport328_suffix_043, ridgeSupport328_suffix_044, ridgeSupport328_suffix_045, ridgeSupport328_suffix_046, ridgeSupport328_suffix_047, ridgeSupport328_suffix_048, ridgeSupport328_suffix_049, ridgeSupport328_suffix_050, ridgeSupport328_suffix_051, ridgeSupport328_suffix_052, ridgeSupport328_suffix_053, ridgeSupport328_suffix_054, ridgeSupport328_suffix_055, ridgeSupport328_suffix_056, ridgeSupport328_suffix_057, ridgeSupport328_suffix_058, ridgeSupport328_suffix_059, ridgeSupport328_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport328_000_mask, ridgeSupport328_001_mask, ridgeSupport328_002_mask, ridgeSupport328_003_mask, ridgeSupport328_004_mask, ridgeSupport328_005_mask, ridgeSupport328_006_mask, ridgeSupport328_007_mask, ridgeSupport328_008_mask, ridgeSupport328_009_mask, ridgeSupport328_010_mask, ridgeSupport328_011_mask, ridgeSupport328_012_mask, ridgeSupport328_013_mask, ridgeSupport328_014_mask, ridgeSupport328_015_mask, ridgeSupport328_016_mask, ridgeSupport328_017_mask, ridgeSupport328_018_mask, ridgeSupport328_019_mask, ridgeSupport328_020_mask, ridgeSupport328_021_mask, ridgeSupport328_022_mask, ridgeSupport328_023_mask, ridgeSupport328_024_mask, ridgeSupport328_025_mask, ridgeSupport328_026_mask, ridgeSupport328_027_mask, ridgeSupport328_028_mask, ridgeSupport328_029_mask, ridgeSupport328_030_mask, ridgeSupport328_031_mask, ridgeSupport328_032_mask, ridgeSupport328_033_mask, ridgeSupport328_034_mask, ridgeSupport328_035_mask, ridgeSupport328_036_mask, ridgeSupport328_037_mask, ridgeSupport328_038_mask, ridgeSupport328_039_mask, ridgeSupport328_040_mask, ridgeSupport328_041_mask, ridgeSupport328_042_mask, ridgeSupport328_043_mask, ridgeSupport328_044_mask, ridgeSupport328_045_mask, ridgeSupport328_046_mask, ridgeSupport328_047_mask, ridgeSupport328_048_mask, ridgeSupport328_049_mask, ridgeSupport328_050_mask, ridgeSupport328_051_mask, ridgeSupport328_052_mask, ridgeSupport328_053_mask, ridgeSupport328_054_mask, ridgeSupport328_055_mask, ridgeSupport328_056_mask, ridgeSupport328_057_mask, ridgeSupport328_058_mask, ridgeSupport328_059_mask]
    decide +kernel
  · rw [ridgeSupport328_eq]
    simp only [ridgeSupport328_suffix_000, ridgeSupport328_suffix_001, ridgeSupport328_suffix_002, ridgeSupport328_suffix_003, ridgeSupport328_suffix_004, ridgeSupport328_suffix_005, ridgeSupport328_suffix_006, ridgeSupport328_suffix_007, ridgeSupport328_suffix_008, ridgeSupport328_suffix_009, ridgeSupport328_suffix_010, ridgeSupport328_suffix_011, ridgeSupport328_suffix_012, ridgeSupport328_suffix_013, ridgeSupport328_suffix_014, ridgeSupport328_suffix_015, ridgeSupport328_suffix_016, ridgeSupport328_suffix_017, ridgeSupport328_suffix_018, ridgeSupport328_suffix_019, ridgeSupport328_suffix_020, ridgeSupport328_suffix_021, ridgeSupport328_suffix_022, ridgeSupport328_suffix_023, ridgeSupport328_suffix_024, ridgeSupport328_suffix_025, ridgeSupport328_suffix_026, ridgeSupport328_suffix_027, ridgeSupport328_suffix_028, ridgeSupport328_suffix_029, ridgeSupport328_suffix_030, ridgeSupport328_suffix_031, ridgeSupport328_suffix_032, ridgeSupport328_suffix_033, ridgeSupport328_suffix_034, ridgeSupport328_suffix_035, ridgeSupport328_suffix_036, ridgeSupport328_suffix_037, ridgeSupport328_suffix_038, ridgeSupport328_suffix_039, ridgeSupport328_suffix_040, ridgeSupport328_suffix_041, ridgeSupport328_suffix_042, ridgeSupport328_suffix_043, ridgeSupport328_suffix_044, ridgeSupport328_suffix_045, ridgeSupport328_suffix_046, ridgeSupport328_suffix_047, ridgeSupport328_suffix_048, ridgeSupport328_suffix_049, ridgeSupport328_suffix_050, ridgeSupport328_suffix_051, ridgeSupport328_suffix_052, ridgeSupport328_suffix_053, ridgeSupport328_suffix_054, ridgeSupport328_suffix_055, ridgeSupport328_suffix_056, ridgeSupport328_suffix_057, ridgeSupport328_suffix_058, ridgeSupport328_suffix_059, ridgeSupport328_suffix_060, List.all_append, List.all_nil, ridgeSupport328_000_checked, ridgeSupport328_001_checked, ridgeSupport328_002_checked, ridgeSupport328_003_checked, ridgeSupport328_004_checked, ridgeSupport328_005_checked, ridgeSupport328_006_checked, ridgeSupport328_007_checked, ridgeSupport328_008_checked, ridgeSupport328_009_checked, ridgeSupport328_010_checked, ridgeSupport328_011_checked, ridgeSupport328_012_checked, ridgeSupport328_013_checked, ridgeSupport328_014_checked, ridgeSupport328_015_checked, ridgeSupport328_016_checked, ridgeSupport328_017_checked, ridgeSupport328_018_checked, ridgeSupport328_019_checked, ridgeSupport328_020_checked, ridgeSupport328_021_checked, ridgeSupport328_022_checked, ridgeSupport328_023_checked, ridgeSupport328_024_checked, ridgeSupport328_025_checked, ridgeSupport328_026_checked, ridgeSupport328_027_checked, ridgeSupport328_028_checked, ridgeSupport328_029_checked, ridgeSupport328_030_checked, ridgeSupport328_031_checked, ridgeSupport328_032_checked, ridgeSupport328_033_checked, ridgeSupport328_034_checked, ridgeSupport328_035_checked, ridgeSupport328_036_checked, ridgeSupport328_037_checked, ridgeSupport328_038_checked, ridgeSupport328_039_checked, ridgeSupport328_040_checked, ridgeSupport328_041_checked, ridgeSupport328_042_checked, ridgeSupport328_043_checked, ridgeSupport328_044_checked, ridgeSupport328_045_checked, ridgeSupport328_046_checked, ridgeSupport328_047_checked, ridgeSupport328_048_checked, ridgeSupport328_049_checked, ridgeSupport328_050_checked, ridgeSupport328_051_checked, ridgeSupport328_052_checked, ridgeSupport328_053_checked, ridgeSupport328_054_checked, ridgeSupport328_055_checked, ridgeSupport328_056_checked, ridgeSupport328_057_checked, ridgeSupport328_058_checked, ridgeSupport328_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
