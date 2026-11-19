module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport388Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 388 060 15
cert_ridgeSupport_suffix_decode_2 388 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 388 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 388 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 388 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 388 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 388 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 388 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 388 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 388 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 388 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 388 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 388 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 388 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 388 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 388 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 388 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 388 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 388 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 388 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 388 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 388 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 388 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 388 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 388 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 388 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 388 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 388 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 388 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 388 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 388 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 388 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 388 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 388 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 388 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 388 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 388 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 388 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 388 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 388 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 388 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 388 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 388 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 388 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 388 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 388 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 388 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 388 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 388 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 388 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 388 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 388 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 388 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 388 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 388 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 388 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 388 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 388 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 388 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 388 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 388 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 388
theorem ridgeTest_large_388 : ridgeTest 388 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport388_eq]
    simp only [ridgeSupport388_suffix_000, ridgeSupport388_suffix_001, ridgeSupport388_suffix_002, ridgeSupport388_suffix_003, ridgeSupport388_suffix_004, ridgeSupport388_suffix_005, ridgeSupport388_suffix_006, ridgeSupport388_suffix_007, ridgeSupport388_suffix_008, ridgeSupport388_suffix_009, ridgeSupport388_suffix_010, ridgeSupport388_suffix_011, ridgeSupport388_suffix_012, ridgeSupport388_suffix_013, ridgeSupport388_suffix_014, ridgeSupport388_suffix_015, ridgeSupport388_suffix_016, ridgeSupport388_suffix_017, ridgeSupport388_suffix_018, ridgeSupport388_suffix_019, ridgeSupport388_suffix_020, ridgeSupport388_suffix_021, ridgeSupport388_suffix_022, ridgeSupport388_suffix_023, ridgeSupport388_suffix_024, ridgeSupport388_suffix_025, ridgeSupport388_suffix_026, ridgeSupport388_suffix_027, ridgeSupport388_suffix_028, ridgeSupport388_suffix_029, ridgeSupport388_suffix_030, ridgeSupport388_suffix_031, ridgeSupport388_suffix_032, ridgeSupport388_suffix_033, ridgeSupport388_suffix_034, ridgeSupport388_suffix_035, ridgeSupport388_suffix_036, ridgeSupport388_suffix_037, ridgeSupport388_suffix_038, ridgeSupport388_suffix_039, ridgeSupport388_suffix_040, ridgeSupport388_suffix_041, ridgeSupport388_suffix_042, ridgeSupport388_suffix_043, ridgeSupport388_suffix_044, ridgeSupport388_suffix_045, ridgeSupport388_suffix_046, ridgeSupport388_suffix_047, ridgeSupport388_suffix_048, ridgeSupport388_suffix_049, ridgeSupport388_suffix_050, ridgeSupport388_suffix_051, ridgeSupport388_suffix_052, ridgeSupport388_suffix_053, ridgeSupport388_suffix_054, ridgeSupport388_suffix_055, ridgeSupport388_suffix_056, ridgeSupport388_suffix_057, ridgeSupport388_suffix_058, ridgeSupport388_suffix_059, ridgeSupport388_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport388_000_mask, ridgeSupport388_001_mask, ridgeSupport388_002_mask, ridgeSupport388_003_mask, ridgeSupport388_004_mask, ridgeSupport388_005_mask, ridgeSupport388_006_mask, ridgeSupport388_007_mask, ridgeSupport388_008_mask, ridgeSupport388_009_mask, ridgeSupport388_010_mask, ridgeSupport388_011_mask, ridgeSupport388_012_mask, ridgeSupport388_013_mask, ridgeSupport388_014_mask, ridgeSupport388_015_mask, ridgeSupport388_016_mask, ridgeSupport388_017_mask, ridgeSupport388_018_mask, ridgeSupport388_019_mask, ridgeSupport388_020_mask, ridgeSupport388_021_mask, ridgeSupport388_022_mask, ridgeSupport388_023_mask, ridgeSupport388_024_mask, ridgeSupport388_025_mask, ridgeSupport388_026_mask, ridgeSupport388_027_mask, ridgeSupport388_028_mask, ridgeSupport388_029_mask, ridgeSupport388_030_mask, ridgeSupport388_031_mask, ridgeSupport388_032_mask, ridgeSupport388_033_mask, ridgeSupport388_034_mask, ridgeSupport388_035_mask, ridgeSupport388_036_mask, ridgeSupport388_037_mask, ridgeSupport388_038_mask, ridgeSupport388_039_mask, ridgeSupport388_040_mask, ridgeSupport388_041_mask, ridgeSupport388_042_mask, ridgeSupport388_043_mask, ridgeSupport388_044_mask, ridgeSupport388_045_mask, ridgeSupport388_046_mask, ridgeSupport388_047_mask, ridgeSupport388_048_mask, ridgeSupport388_049_mask, ridgeSupport388_050_mask, ridgeSupport388_051_mask, ridgeSupport388_052_mask, ridgeSupport388_053_mask, ridgeSupport388_054_mask, ridgeSupport388_055_mask, ridgeSupport388_056_mask, ridgeSupport388_057_mask, ridgeSupport388_058_mask, ridgeSupport388_059_mask]
    decide +kernel
  · rw [ridgeSupport388_eq]
    simp only [ridgeSupport388_suffix_000, ridgeSupport388_suffix_001, ridgeSupport388_suffix_002, ridgeSupport388_suffix_003, ridgeSupport388_suffix_004, ridgeSupport388_suffix_005, ridgeSupport388_suffix_006, ridgeSupport388_suffix_007, ridgeSupport388_suffix_008, ridgeSupport388_suffix_009, ridgeSupport388_suffix_010, ridgeSupport388_suffix_011, ridgeSupport388_suffix_012, ridgeSupport388_suffix_013, ridgeSupport388_suffix_014, ridgeSupport388_suffix_015, ridgeSupport388_suffix_016, ridgeSupport388_suffix_017, ridgeSupport388_suffix_018, ridgeSupport388_suffix_019, ridgeSupport388_suffix_020, ridgeSupport388_suffix_021, ridgeSupport388_suffix_022, ridgeSupport388_suffix_023, ridgeSupport388_suffix_024, ridgeSupport388_suffix_025, ridgeSupport388_suffix_026, ridgeSupport388_suffix_027, ridgeSupport388_suffix_028, ridgeSupport388_suffix_029, ridgeSupport388_suffix_030, ridgeSupport388_suffix_031, ridgeSupport388_suffix_032, ridgeSupport388_suffix_033, ridgeSupport388_suffix_034, ridgeSupport388_suffix_035, ridgeSupport388_suffix_036, ridgeSupport388_suffix_037, ridgeSupport388_suffix_038, ridgeSupport388_suffix_039, ridgeSupport388_suffix_040, ridgeSupport388_suffix_041, ridgeSupport388_suffix_042, ridgeSupport388_suffix_043, ridgeSupport388_suffix_044, ridgeSupport388_suffix_045, ridgeSupport388_suffix_046, ridgeSupport388_suffix_047, ridgeSupport388_suffix_048, ridgeSupport388_suffix_049, ridgeSupport388_suffix_050, ridgeSupport388_suffix_051, ridgeSupport388_suffix_052, ridgeSupport388_suffix_053, ridgeSupport388_suffix_054, ridgeSupport388_suffix_055, ridgeSupport388_suffix_056, ridgeSupport388_suffix_057, ridgeSupport388_suffix_058, ridgeSupport388_suffix_059, ridgeSupport388_suffix_060, List.all_append, List.all_nil, ridgeSupport388_000_checked, ridgeSupport388_001_checked, ridgeSupport388_002_checked, ridgeSupport388_003_checked, ridgeSupport388_004_checked, ridgeSupport388_005_checked, ridgeSupport388_006_checked, ridgeSupport388_007_checked, ridgeSupport388_008_checked, ridgeSupport388_009_checked, ridgeSupport388_010_checked, ridgeSupport388_011_checked, ridgeSupport388_012_checked, ridgeSupport388_013_checked, ridgeSupport388_014_checked, ridgeSupport388_015_checked, ridgeSupport388_016_checked, ridgeSupport388_017_checked, ridgeSupport388_018_checked, ridgeSupport388_019_checked, ridgeSupport388_020_checked, ridgeSupport388_021_checked, ridgeSupport388_022_checked, ridgeSupport388_023_checked, ridgeSupport388_024_checked, ridgeSupport388_025_checked, ridgeSupport388_026_checked, ridgeSupport388_027_checked, ridgeSupport388_028_checked, ridgeSupport388_029_checked, ridgeSupport388_030_checked, ridgeSupport388_031_checked, ridgeSupport388_032_checked, ridgeSupport388_033_checked, ridgeSupport388_034_checked, ridgeSupport388_035_checked, ridgeSupport388_036_checked, ridgeSupport388_037_checked, ridgeSupport388_038_checked, ridgeSupport388_039_checked, ridgeSupport388_040_checked, ridgeSupport388_041_checked, ridgeSupport388_042_checked, ridgeSupport388_043_checked, ridgeSupport388_044_checked, ridgeSupport388_045_checked, ridgeSupport388_046_checked, ridgeSupport388_047_checked, ridgeSupport388_048_checked, ridgeSupport388_049_checked, ridgeSupport388_050_checked, ridgeSupport388_051_checked, ridgeSupport388_052_checked, ridgeSupport388_053_checked, ridgeSupport388_054_checked, ridgeSupport388_055_checked, ridgeSupport388_056_checked, ridgeSupport388_057_checked, ridgeSupport388_058_checked, ridgeSupport388_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
