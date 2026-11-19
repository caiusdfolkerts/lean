module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport392Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 392 060 15
cert_ridgeSupport_suffix_decode_2 392 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 392 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 392 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 392 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 392 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 392 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 392 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 392 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 392 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 392 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 392 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 392 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 392 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 392 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 392 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 392 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 392 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 392 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 392 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 392 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 392 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 392 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 392 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 392 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 392 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 392 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 392 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 392 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 392 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 392 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 392 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 392 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 392 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 392 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 392 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 392 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 392 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 392 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 392 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 392 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 392 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 392 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 392 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 392 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 392 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 392 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 392 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 392 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 392 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 392 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 392 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 392 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 392 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 392 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 392 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 392 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 392 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 392 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 392 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 392 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 392
theorem ridgeTest_large_392 : ridgeTest 392 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport392_eq]
    simp only [ridgeSupport392_suffix_000, ridgeSupport392_suffix_001, ridgeSupport392_suffix_002, ridgeSupport392_suffix_003, ridgeSupport392_suffix_004, ridgeSupport392_suffix_005, ridgeSupport392_suffix_006, ridgeSupport392_suffix_007, ridgeSupport392_suffix_008, ridgeSupport392_suffix_009, ridgeSupport392_suffix_010, ridgeSupport392_suffix_011, ridgeSupport392_suffix_012, ridgeSupport392_suffix_013, ridgeSupport392_suffix_014, ridgeSupport392_suffix_015, ridgeSupport392_suffix_016, ridgeSupport392_suffix_017, ridgeSupport392_suffix_018, ridgeSupport392_suffix_019, ridgeSupport392_suffix_020, ridgeSupport392_suffix_021, ridgeSupport392_suffix_022, ridgeSupport392_suffix_023, ridgeSupport392_suffix_024, ridgeSupport392_suffix_025, ridgeSupport392_suffix_026, ridgeSupport392_suffix_027, ridgeSupport392_suffix_028, ridgeSupport392_suffix_029, ridgeSupport392_suffix_030, ridgeSupport392_suffix_031, ridgeSupport392_suffix_032, ridgeSupport392_suffix_033, ridgeSupport392_suffix_034, ridgeSupport392_suffix_035, ridgeSupport392_suffix_036, ridgeSupport392_suffix_037, ridgeSupport392_suffix_038, ridgeSupport392_suffix_039, ridgeSupport392_suffix_040, ridgeSupport392_suffix_041, ridgeSupport392_suffix_042, ridgeSupport392_suffix_043, ridgeSupport392_suffix_044, ridgeSupport392_suffix_045, ridgeSupport392_suffix_046, ridgeSupport392_suffix_047, ridgeSupport392_suffix_048, ridgeSupport392_suffix_049, ridgeSupport392_suffix_050, ridgeSupport392_suffix_051, ridgeSupport392_suffix_052, ridgeSupport392_suffix_053, ridgeSupport392_suffix_054, ridgeSupport392_suffix_055, ridgeSupport392_suffix_056, ridgeSupport392_suffix_057, ridgeSupport392_suffix_058, ridgeSupport392_suffix_059, ridgeSupport392_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport392_000_mask, ridgeSupport392_001_mask, ridgeSupport392_002_mask, ridgeSupport392_003_mask, ridgeSupport392_004_mask, ridgeSupport392_005_mask, ridgeSupport392_006_mask, ridgeSupport392_007_mask, ridgeSupport392_008_mask, ridgeSupport392_009_mask, ridgeSupport392_010_mask, ridgeSupport392_011_mask, ridgeSupport392_012_mask, ridgeSupport392_013_mask, ridgeSupport392_014_mask, ridgeSupport392_015_mask, ridgeSupport392_016_mask, ridgeSupport392_017_mask, ridgeSupport392_018_mask, ridgeSupport392_019_mask, ridgeSupport392_020_mask, ridgeSupport392_021_mask, ridgeSupport392_022_mask, ridgeSupport392_023_mask, ridgeSupport392_024_mask, ridgeSupport392_025_mask, ridgeSupport392_026_mask, ridgeSupport392_027_mask, ridgeSupport392_028_mask, ridgeSupport392_029_mask, ridgeSupport392_030_mask, ridgeSupport392_031_mask, ridgeSupport392_032_mask, ridgeSupport392_033_mask, ridgeSupport392_034_mask, ridgeSupport392_035_mask, ridgeSupport392_036_mask, ridgeSupport392_037_mask, ridgeSupport392_038_mask, ridgeSupport392_039_mask, ridgeSupport392_040_mask, ridgeSupport392_041_mask, ridgeSupport392_042_mask, ridgeSupport392_043_mask, ridgeSupport392_044_mask, ridgeSupport392_045_mask, ridgeSupport392_046_mask, ridgeSupport392_047_mask, ridgeSupport392_048_mask, ridgeSupport392_049_mask, ridgeSupport392_050_mask, ridgeSupport392_051_mask, ridgeSupport392_052_mask, ridgeSupport392_053_mask, ridgeSupport392_054_mask, ridgeSupport392_055_mask, ridgeSupport392_056_mask, ridgeSupport392_057_mask, ridgeSupport392_058_mask, ridgeSupport392_059_mask]
    decide +kernel
  · rw [ridgeSupport392_eq]
    simp only [ridgeSupport392_suffix_000, ridgeSupport392_suffix_001, ridgeSupport392_suffix_002, ridgeSupport392_suffix_003, ridgeSupport392_suffix_004, ridgeSupport392_suffix_005, ridgeSupport392_suffix_006, ridgeSupport392_suffix_007, ridgeSupport392_suffix_008, ridgeSupport392_suffix_009, ridgeSupport392_suffix_010, ridgeSupport392_suffix_011, ridgeSupport392_suffix_012, ridgeSupport392_suffix_013, ridgeSupport392_suffix_014, ridgeSupport392_suffix_015, ridgeSupport392_suffix_016, ridgeSupport392_suffix_017, ridgeSupport392_suffix_018, ridgeSupport392_suffix_019, ridgeSupport392_suffix_020, ridgeSupport392_suffix_021, ridgeSupport392_suffix_022, ridgeSupport392_suffix_023, ridgeSupport392_suffix_024, ridgeSupport392_suffix_025, ridgeSupport392_suffix_026, ridgeSupport392_suffix_027, ridgeSupport392_suffix_028, ridgeSupport392_suffix_029, ridgeSupport392_suffix_030, ridgeSupport392_suffix_031, ridgeSupport392_suffix_032, ridgeSupport392_suffix_033, ridgeSupport392_suffix_034, ridgeSupport392_suffix_035, ridgeSupport392_suffix_036, ridgeSupport392_suffix_037, ridgeSupport392_suffix_038, ridgeSupport392_suffix_039, ridgeSupport392_suffix_040, ridgeSupport392_suffix_041, ridgeSupport392_suffix_042, ridgeSupport392_suffix_043, ridgeSupport392_suffix_044, ridgeSupport392_suffix_045, ridgeSupport392_suffix_046, ridgeSupport392_suffix_047, ridgeSupport392_suffix_048, ridgeSupport392_suffix_049, ridgeSupport392_suffix_050, ridgeSupport392_suffix_051, ridgeSupport392_suffix_052, ridgeSupport392_suffix_053, ridgeSupport392_suffix_054, ridgeSupport392_suffix_055, ridgeSupport392_suffix_056, ridgeSupport392_suffix_057, ridgeSupport392_suffix_058, ridgeSupport392_suffix_059, ridgeSupport392_suffix_060, List.all_append, List.all_nil, ridgeSupport392_000_checked, ridgeSupport392_001_checked, ridgeSupport392_002_checked, ridgeSupport392_003_checked, ridgeSupport392_004_checked, ridgeSupport392_005_checked, ridgeSupport392_006_checked, ridgeSupport392_007_checked, ridgeSupport392_008_checked, ridgeSupport392_009_checked, ridgeSupport392_010_checked, ridgeSupport392_011_checked, ridgeSupport392_012_checked, ridgeSupport392_013_checked, ridgeSupport392_014_checked, ridgeSupport392_015_checked, ridgeSupport392_016_checked, ridgeSupport392_017_checked, ridgeSupport392_018_checked, ridgeSupport392_019_checked, ridgeSupport392_020_checked, ridgeSupport392_021_checked, ridgeSupport392_022_checked, ridgeSupport392_023_checked, ridgeSupport392_024_checked, ridgeSupport392_025_checked, ridgeSupport392_026_checked, ridgeSupport392_027_checked, ridgeSupport392_028_checked, ridgeSupport392_029_checked, ridgeSupport392_030_checked, ridgeSupport392_031_checked, ridgeSupport392_032_checked, ridgeSupport392_033_checked, ridgeSupport392_034_checked, ridgeSupport392_035_checked, ridgeSupport392_036_checked, ridgeSupport392_037_checked, ridgeSupport392_038_checked, ridgeSupport392_039_checked, ridgeSupport392_040_checked, ridgeSupport392_041_checked, ridgeSupport392_042_checked, ridgeSupport392_043_checked, ridgeSupport392_044_checked, ridgeSupport392_045_checked, ridgeSupport392_046_checked, ridgeSupport392_047_checked, ridgeSupport392_048_checked, ridgeSupport392_049_checked, ridgeSupport392_050_checked, ridgeSupport392_051_checked, ridgeSupport392_052_checked, ridgeSupport392_053_checked, ridgeSupport392_054_checked, ridgeSupport392_055_checked, ridgeSupport392_056_checked, ridgeSupport392_057_checked, ridgeSupport392_058_checked, ridgeSupport392_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
