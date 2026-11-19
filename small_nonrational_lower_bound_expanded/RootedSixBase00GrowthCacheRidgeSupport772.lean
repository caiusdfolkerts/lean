module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport772Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 772 060 15
cert_ridgeSupport_suffix_decode_2 772 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 772 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 772 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 772 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 772 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 772 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 772 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 772 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 772 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 772 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 772 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 772 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 772 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 772 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 772 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 772 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 772 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 772 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 772 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 772 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 772 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 772 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 772 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 772 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 772 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 772 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 772 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 772 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 772 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 772 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 772 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 772 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 772 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 772 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 772 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 772 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 772 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 772 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 772 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 772 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 772 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 772 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 772 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 772 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 772 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 772 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 772 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 772 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 772 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 772 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 772 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 772 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 772 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 772 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 772 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 772 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 772 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 772 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 772 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 772 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 772
theorem ridgeTest_large_772 : ridgeTest 772 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, ridgeSupport772_suffix_010, ridgeSupport772_suffix_011, ridgeSupport772_suffix_012, ridgeSupport772_suffix_013, ridgeSupport772_suffix_014, ridgeSupport772_suffix_015, ridgeSupport772_suffix_016, ridgeSupport772_suffix_017, ridgeSupport772_suffix_018, ridgeSupport772_suffix_019, ridgeSupport772_suffix_020, ridgeSupport772_suffix_021, ridgeSupport772_suffix_022, ridgeSupport772_suffix_023, ridgeSupport772_suffix_024, ridgeSupport772_suffix_025, ridgeSupport772_suffix_026, ridgeSupport772_suffix_027, ridgeSupport772_suffix_028, ridgeSupport772_suffix_029, ridgeSupport772_suffix_030, ridgeSupport772_suffix_031, ridgeSupport772_suffix_032, ridgeSupport772_suffix_033, ridgeSupport772_suffix_034, ridgeSupport772_suffix_035, ridgeSupport772_suffix_036, ridgeSupport772_suffix_037, ridgeSupport772_suffix_038, ridgeSupport772_suffix_039, ridgeSupport772_suffix_040, ridgeSupport772_suffix_041, ridgeSupport772_suffix_042, ridgeSupport772_suffix_043, ridgeSupport772_suffix_044, ridgeSupport772_suffix_045, ridgeSupport772_suffix_046, ridgeSupport772_suffix_047, ridgeSupport772_suffix_048, ridgeSupport772_suffix_049, ridgeSupport772_suffix_050, ridgeSupport772_suffix_051, ridgeSupport772_suffix_052, ridgeSupport772_suffix_053, ridgeSupport772_suffix_054, ridgeSupport772_suffix_055, ridgeSupport772_suffix_056, ridgeSupport772_suffix_057, ridgeSupport772_suffix_058, ridgeSupport772_suffix_059, ridgeSupport772_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport772_000_mask, ridgeSupport772_001_mask, ridgeSupport772_002_mask, ridgeSupport772_003_mask, ridgeSupport772_004_mask, ridgeSupport772_005_mask, ridgeSupport772_006_mask, ridgeSupport772_007_mask, ridgeSupport772_008_mask, ridgeSupport772_009_mask, ridgeSupport772_010_mask, ridgeSupport772_011_mask, ridgeSupport772_012_mask, ridgeSupport772_013_mask, ridgeSupport772_014_mask, ridgeSupport772_015_mask, ridgeSupport772_016_mask, ridgeSupport772_017_mask, ridgeSupport772_018_mask, ridgeSupport772_019_mask, ridgeSupport772_020_mask, ridgeSupport772_021_mask, ridgeSupport772_022_mask, ridgeSupport772_023_mask, ridgeSupport772_024_mask, ridgeSupport772_025_mask, ridgeSupport772_026_mask, ridgeSupport772_027_mask, ridgeSupport772_028_mask, ridgeSupport772_029_mask, ridgeSupport772_030_mask, ridgeSupport772_031_mask, ridgeSupport772_032_mask, ridgeSupport772_033_mask, ridgeSupport772_034_mask, ridgeSupport772_035_mask, ridgeSupport772_036_mask, ridgeSupport772_037_mask, ridgeSupport772_038_mask, ridgeSupport772_039_mask, ridgeSupport772_040_mask, ridgeSupport772_041_mask, ridgeSupport772_042_mask, ridgeSupport772_043_mask, ridgeSupport772_044_mask, ridgeSupport772_045_mask, ridgeSupport772_046_mask, ridgeSupport772_047_mask, ridgeSupport772_048_mask, ridgeSupport772_049_mask, ridgeSupport772_050_mask, ridgeSupport772_051_mask, ridgeSupport772_052_mask, ridgeSupport772_053_mask, ridgeSupport772_054_mask, ridgeSupport772_055_mask, ridgeSupport772_056_mask, ridgeSupport772_057_mask, ridgeSupport772_058_mask, ridgeSupport772_059_mask]
    decide +kernel
  · rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, ridgeSupport772_suffix_010, ridgeSupport772_suffix_011, ridgeSupport772_suffix_012, ridgeSupport772_suffix_013, ridgeSupport772_suffix_014, ridgeSupport772_suffix_015, ridgeSupport772_suffix_016, ridgeSupport772_suffix_017, ridgeSupport772_suffix_018, ridgeSupport772_suffix_019, ridgeSupport772_suffix_020, ridgeSupport772_suffix_021, ridgeSupport772_suffix_022, ridgeSupport772_suffix_023, ridgeSupport772_suffix_024, ridgeSupport772_suffix_025, ridgeSupport772_suffix_026, ridgeSupport772_suffix_027, ridgeSupport772_suffix_028, ridgeSupport772_suffix_029, ridgeSupport772_suffix_030, ridgeSupport772_suffix_031, ridgeSupport772_suffix_032, ridgeSupport772_suffix_033, ridgeSupport772_suffix_034, ridgeSupport772_suffix_035, ridgeSupport772_suffix_036, ridgeSupport772_suffix_037, ridgeSupport772_suffix_038, ridgeSupport772_suffix_039, ridgeSupport772_suffix_040, ridgeSupport772_suffix_041, ridgeSupport772_suffix_042, ridgeSupport772_suffix_043, ridgeSupport772_suffix_044, ridgeSupport772_suffix_045, ridgeSupport772_suffix_046, ridgeSupport772_suffix_047, ridgeSupport772_suffix_048, ridgeSupport772_suffix_049, ridgeSupport772_suffix_050, ridgeSupport772_suffix_051, ridgeSupport772_suffix_052, ridgeSupport772_suffix_053, ridgeSupport772_suffix_054, ridgeSupport772_suffix_055, ridgeSupport772_suffix_056, ridgeSupport772_suffix_057, ridgeSupport772_suffix_058, ridgeSupport772_suffix_059, ridgeSupport772_suffix_060, List.all_append, List.all_nil, ridgeSupport772_000_checked, ridgeSupport772_001_checked, ridgeSupport772_002_checked, ridgeSupport772_003_checked, ridgeSupport772_004_checked, ridgeSupport772_005_checked, ridgeSupport772_006_checked, ridgeSupport772_007_checked, ridgeSupport772_008_checked, ridgeSupport772_009_checked, ridgeSupport772_010_checked, ridgeSupport772_011_checked, ridgeSupport772_012_checked, ridgeSupport772_013_checked, ridgeSupport772_014_checked, ridgeSupport772_015_checked, ridgeSupport772_016_checked, ridgeSupport772_017_checked, ridgeSupport772_018_checked, ridgeSupport772_019_checked, ridgeSupport772_020_checked, ridgeSupport772_021_checked, ridgeSupport772_022_checked, ridgeSupport772_023_checked, ridgeSupport772_024_checked, ridgeSupport772_025_checked, ridgeSupport772_026_checked, ridgeSupport772_027_checked, ridgeSupport772_028_checked, ridgeSupport772_029_checked, ridgeSupport772_030_checked, ridgeSupport772_031_checked, ridgeSupport772_032_checked, ridgeSupport772_033_checked, ridgeSupport772_034_checked, ridgeSupport772_035_checked, ridgeSupport772_036_checked, ridgeSupport772_037_checked, ridgeSupport772_038_checked, ridgeSupport772_039_checked, ridgeSupport772_040_checked, ridgeSupport772_041_checked, ridgeSupport772_042_checked, ridgeSupport772_043_checked, ridgeSupport772_044_checked, ridgeSupport772_045_checked, ridgeSupport772_046_checked, ridgeSupport772_047_checked, ridgeSupport772_048_checked, ridgeSupport772_049_checked, ridgeSupport772_050_checked, ridgeSupport772_051_checked, ridgeSupport772_052_checked, ridgeSupport772_053_checked, ridgeSupport772_054_checked, ridgeSupport772_055_checked, ridgeSupport772_056_checked, ridgeSupport772_057_checked, ridgeSupport772_058_checked, ridgeSupport772_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
