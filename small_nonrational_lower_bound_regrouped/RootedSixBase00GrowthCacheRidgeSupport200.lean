module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport200Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 200 060 15
cert_ridgeSupport_suffix_decode_2 200 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 200 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 200 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 200 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 200 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 200 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 200 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 200 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 200 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 200 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 200 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 200 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 200 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 200 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 200 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 200 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 200 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 200 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 200 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 200 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 200 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 200 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 200 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 200 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 200 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 200 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 200 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 200 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 200 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 200 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 200 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 200 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 200 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 200 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 200 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 200 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 200 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 200 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 200 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 200 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 200 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 200 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 200 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 200 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 200 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 200 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 200 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 200 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 200 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 200 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 200 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 200 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 200 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 200 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 200 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 200 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 200 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 200 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 200 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 200 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 200
theorem ridgeTest_large_200 : ridgeTest 200 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, ridgeSupport200_suffix_012, ridgeSupport200_suffix_013, ridgeSupport200_suffix_014, ridgeSupport200_suffix_015, ridgeSupport200_suffix_016, ridgeSupport200_suffix_017, ridgeSupport200_suffix_018, ridgeSupport200_suffix_019, ridgeSupport200_suffix_020, ridgeSupport200_suffix_021, ridgeSupport200_suffix_022, ridgeSupport200_suffix_023, ridgeSupport200_suffix_024, ridgeSupport200_suffix_025, ridgeSupport200_suffix_026, ridgeSupport200_suffix_027, ridgeSupport200_suffix_028, ridgeSupport200_suffix_029, ridgeSupport200_suffix_030, ridgeSupport200_suffix_031, ridgeSupport200_suffix_032, ridgeSupport200_suffix_033, ridgeSupport200_suffix_034, ridgeSupport200_suffix_035, ridgeSupport200_suffix_036, ridgeSupport200_suffix_037, ridgeSupport200_suffix_038, ridgeSupport200_suffix_039, ridgeSupport200_suffix_040, ridgeSupport200_suffix_041, ridgeSupport200_suffix_042, ridgeSupport200_suffix_043, ridgeSupport200_suffix_044, ridgeSupport200_suffix_045, ridgeSupport200_suffix_046, ridgeSupport200_suffix_047, ridgeSupport200_suffix_048, ridgeSupport200_suffix_049, ridgeSupport200_suffix_050, ridgeSupport200_suffix_051, ridgeSupport200_suffix_052, ridgeSupport200_suffix_053, ridgeSupport200_suffix_054, ridgeSupport200_suffix_055, ridgeSupport200_suffix_056, ridgeSupport200_suffix_057, ridgeSupport200_suffix_058, ridgeSupport200_suffix_059, ridgeSupport200_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport200_000_mask, ridgeSupport200_001_mask, ridgeSupport200_002_mask, ridgeSupport200_003_mask, ridgeSupport200_004_mask, ridgeSupport200_005_mask, ridgeSupport200_006_mask, ridgeSupport200_007_mask, ridgeSupport200_008_mask, ridgeSupport200_009_mask, ridgeSupport200_010_mask, ridgeSupport200_011_mask, ridgeSupport200_012_mask, ridgeSupport200_013_mask, ridgeSupport200_014_mask, ridgeSupport200_015_mask, ridgeSupport200_016_mask, ridgeSupport200_017_mask, ridgeSupport200_018_mask, ridgeSupport200_019_mask, ridgeSupport200_020_mask, ridgeSupport200_021_mask, ridgeSupport200_022_mask, ridgeSupport200_023_mask, ridgeSupport200_024_mask, ridgeSupport200_025_mask, ridgeSupport200_026_mask, ridgeSupport200_027_mask, ridgeSupport200_028_mask, ridgeSupport200_029_mask, ridgeSupport200_030_mask, ridgeSupport200_031_mask, ridgeSupport200_032_mask, ridgeSupport200_033_mask, ridgeSupport200_034_mask, ridgeSupport200_035_mask, ridgeSupport200_036_mask, ridgeSupport200_037_mask, ridgeSupport200_038_mask, ridgeSupport200_039_mask, ridgeSupport200_040_mask, ridgeSupport200_041_mask, ridgeSupport200_042_mask, ridgeSupport200_043_mask, ridgeSupport200_044_mask, ridgeSupport200_045_mask, ridgeSupport200_046_mask, ridgeSupport200_047_mask, ridgeSupport200_048_mask, ridgeSupport200_049_mask, ridgeSupport200_050_mask, ridgeSupport200_051_mask, ridgeSupport200_052_mask, ridgeSupport200_053_mask, ridgeSupport200_054_mask, ridgeSupport200_055_mask, ridgeSupport200_056_mask, ridgeSupport200_057_mask, ridgeSupport200_058_mask, ridgeSupport200_059_mask]
    decide +kernel
  · rw [ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, ridgeSupport200_suffix_012, ridgeSupport200_suffix_013, ridgeSupport200_suffix_014, ridgeSupport200_suffix_015, ridgeSupport200_suffix_016, ridgeSupport200_suffix_017, ridgeSupport200_suffix_018, ridgeSupport200_suffix_019, ridgeSupport200_suffix_020, ridgeSupport200_suffix_021, ridgeSupport200_suffix_022, ridgeSupport200_suffix_023, ridgeSupport200_suffix_024, ridgeSupport200_suffix_025, ridgeSupport200_suffix_026, ridgeSupport200_suffix_027, ridgeSupport200_suffix_028, ridgeSupport200_suffix_029, ridgeSupport200_suffix_030, ridgeSupport200_suffix_031, ridgeSupport200_suffix_032, ridgeSupport200_suffix_033, ridgeSupport200_suffix_034, ridgeSupport200_suffix_035, ridgeSupport200_suffix_036, ridgeSupport200_suffix_037, ridgeSupport200_suffix_038, ridgeSupport200_suffix_039, ridgeSupport200_suffix_040, ridgeSupport200_suffix_041, ridgeSupport200_suffix_042, ridgeSupport200_suffix_043, ridgeSupport200_suffix_044, ridgeSupport200_suffix_045, ridgeSupport200_suffix_046, ridgeSupport200_suffix_047, ridgeSupport200_suffix_048, ridgeSupport200_suffix_049, ridgeSupport200_suffix_050, ridgeSupport200_suffix_051, ridgeSupport200_suffix_052, ridgeSupport200_suffix_053, ridgeSupport200_suffix_054, ridgeSupport200_suffix_055, ridgeSupport200_suffix_056, ridgeSupport200_suffix_057, ridgeSupport200_suffix_058, ridgeSupport200_suffix_059, ridgeSupport200_suffix_060, List.all_append, List.all_nil, ridgeSupport200_000_checked, ridgeSupport200_001_checked, ridgeSupport200_002_checked, ridgeSupport200_003_checked, ridgeSupport200_004_checked, ridgeSupport200_005_checked, ridgeSupport200_006_checked, ridgeSupport200_007_checked, ridgeSupport200_008_checked, ridgeSupport200_009_checked, ridgeSupport200_010_checked, ridgeSupport200_011_checked, ridgeSupport200_012_checked, ridgeSupport200_013_checked, ridgeSupport200_014_checked, ridgeSupport200_015_checked, ridgeSupport200_016_checked, ridgeSupport200_017_checked, ridgeSupport200_018_checked, ridgeSupport200_019_checked, ridgeSupport200_020_checked, ridgeSupport200_021_checked, ridgeSupport200_022_checked, ridgeSupport200_023_checked, ridgeSupport200_024_checked, ridgeSupport200_025_checked, ridgeSupport200_026_checked, ridgeSupport200_027_checked, ridgeSupport200_028_checked, ridgeSupport200_029_checked, ridgeSupport200_030_checked, ridgeSupport200_031_checked, ridgeSupport200_032_checked, ridgeSupport200_033_checked, ridgeSupport200_034_checked, ridgeSupport200_035_checked, ridgeSupport200_036_checked, ridgeSupport200_037_checked, ridgeSupport200_038_checked, ridgeSupport200_039_checked, ridgeSupport200_040_checked, ridgeSupport200_041_checked, ridgeSupport200_042_checked, ridgeSupport200_043_checked, ridgeSupport200_044_checked, ridgeSupport200_045_checked, ridgeSupport200_046_checked, ridgeSupport200_047_checked, ridgeSupport200_048_checked, ridgeSupport200_049_checked, ridgeSupport200_050_checked, ridgeSupport200_051_checked, ridgeSupport200_052_checked, ridgeSupport200_053_checked, ridgeSupport200_054_checked, ridgeSupport200_055_checked, ridgeSupport200_056_checked, ridgeSupport200_057_checked, ridgeSupport200_058_checked, ridgeSupport200_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
