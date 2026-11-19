module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport648Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 648 060 15
cert_ridgeSupport_suffix_decode_2 648 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 648 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 648 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 648 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 648 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 648 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 648 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 648 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 648 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 648 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 648 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 648 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 648 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 648 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 648 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 648 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 648 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 648 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 648 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 648 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 648 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 648 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 648 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 648 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 648 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 648 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 648 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 648 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 648 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 648 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 648 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 648 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 648 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 648 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 648 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 648 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 648 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 648 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 648 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 648 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 648 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 648 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 648 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 648 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 648 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 648 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 648 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 648 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 648 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 648 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 648 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 648 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 648 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 648 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 648 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 648 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 648 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 648 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 648 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 648 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 648
theorem ridgeTest_large_648 : ridgeTest 648 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport648_eq]
    simp only [ridgeSupport648_suffix_000, ridgeSupport648_suffix_001, ridgeSupport648_suffix_002, ridgeSupport648_suffix_003, ridgeSupport648_suffix_004, ridgeSupport648_suffix_005, ridgeSupport648_suffix_006, ridgeSupport648_suffix_007, ridgeSupport648_suffix_008, ridgeSupport648_suffix_009, ridgeSupport648_suffix_010, ridgeSupport648_suffix_011, ridgeSupport648_suffix_012, ridgeSupport648_suffix_013, ridgeSupport648_suffix_014, ridgeSupport648_suffix_015, ridgeSupport648_suffix_016, ridgeSupport648_suffix_017, ridgeSupport648_suffix_018, ridgeSupport648_suffix_019, ridgeSupport648_suffix_020, ridgeSupport648_suffix_021, ridgeSupport648_suffix_022, ridgeSupport648_suffix_023, ridgeSupport648_suffix_024, ridgeSupport648_suffix_025, ridgeSupport648_suffix_026, ridgeSupport648_suffix_027, ridgeSupport648_suffix_028, ridgeSupport648_suffix_029, ridgeSupport648_suffix_030, ridgeSupport648_suffix_031, ridgeSupport648_suffix_032, ridgeSupport648_suffix_033, ridgeSupport648_suffix_034, ridgeSupport648_suffix_035, ridgeSupport648_suffix_036, ridgeSupport648_suffix_037, ridgeSupport648_suffix_038, ridgeSupport648_suffix_039, ridgeSupport648_suffix_040, ridgeSupport648_suffix_041, ridgeSupport648_suffix_042, ridgeSupport648_suffix_043, ridgeSupport648_suffix_044, ridgeSupport648_suffix_045, ridgeSupport648_suffix_046, ridgeSupport648_suffix_047, ridgeSupport648_suffix_048, ridgeSupport648_suffix_049, ridgeSupport648_suffix_050, ridgeSupport648_suffix_051, ridgeSupport648_suffix_052, ridgeSupport648_suffix_053, ridgeSupport648_suffix_054, ridgeSupport648_suffix_055, ridgeSupport648_suffix_056, ridgeSupport648_suffix_057, ridgeSupport648_suffix_058, ridgeSupport648_suffix_059, ridgeSupport648_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport648_000_mask, ridgeSupport648_001_mask, ridgeSupport648_002_mask, ridgeSupport648_003_mask, ridgeSupport648_004_mask, ridgeSupport648_005_mask, ridgeSupport648_006_mask, ridgeSupport648_007_mask, ridgeSupport648_008_mask, ridgeSupport648_009_mask, ridgeSupport648_010_mask, ridgeSupport648_011_mask, ridgeSupport648_012_mask, ridgeSupport648_013_mask, ridgeSupport648_014_mask, ridgeSupport648_015_mask, ridgeSupport648_016_mask, ridgeSupport648_017_mask, ridgeSupport648_018_mask, ridgeSupport648_019_mask, ridgeSupport648_020_mask, ridgeSupport648_021_mask, ridgeSupport648_022_mask, ridgeSupport648_023_mask, ridgeSupport648_024_mask, ridgeSupport648_025_mask, ridgeSupport648_026_mask, ridgeSupport648_027_mask, ridgeSupport648_028_mask, ridgeSupport648_029_mask, ridgeSupport648_030_mask, ridgeSupport648_031_mask, ridgeSupport648_032_mask, ridgeSupport648_033_mask, ridgeSupport648_034_mask, ridgeSupport648_035_mask, ridgeSupport648_036_mask, ridgeSupport648_037_mask, ridgeSupport648_038_mask, ridgeSupport648_039_mask, ridgeSupport648_040_mask, ridgeSupport648_041_mask, ridgeSupport648_042_mask, ridgeSupport648_043_mask, ridgeSupport648_044_mask, ridgeSupport648_045_mask, ridgeSupport648_046_mask, ridgeSupport648_047_mask, ridgeSupport648_048_mask, ridgeSupport648_049_mask, ridgeSupport648_050_mask, ridgeSupport648_051_mask, ridgeSupport648_052_mask, ridgeSupport648_053_mask, ridgeSupport648_054_mask, ridgeSupport648_055_mask, ridgeSupport648_056_mask, ridgeSupport648_057_mask, ridgeSupport648_058_mask, ridgeSupport648_059_mask]
    decide +kernel
  · rw [ridgeSupport648_eq]
    simp only [ridgeSupport648_suffix_000, ridgeSupport648_suffix_001, ridgeSupport648_suffix_002, ridgeSupport648_suffix_003, ridgeSupport648_suffix_004, ridgeSupport648_suffix_005, ridgeSupport648_suffix_006, ridgeSupport648_suffix_007, ridgeSupport648_suffix_008, ridgeSupport648_suffix_009, ridgeSupport648_suffix_010, ridgeSupport648_suffix_011, ridgeSupport648_suffix_012, ridgeSupport648_suffix_013, ridgeSupport648_suffix_014, ridgeSupport648_suffix_015, ridgeSupport648_suffix_016, ridgeSupport648_suffix_017, ridgeSupport648_suffix_018, ridgeSupport648_suffix_019, ridgeSupport648_suffix_020, ridgeSupport648_suffix_021, ridgeSupport648_suffix_022, ridgeSupport648_suffix_023, ridgeSupport648_suffix_024, ridgeSupport648_suffix_025, ridgeSupport648_suffix_026, ridgeSupport648_suffix_027, ridgeSupport648_suffix_028, ridgeSupport648_suffix_029, ridgeSupport648_suffix_030, ridgeSupport648_suffix_031, ridgeSupport648_suffix_032, ridgeSupport648_suffix_033, ridgeSupport648_suffix_034, ridgeSupport648_suffix_035, ridgeSupport648_suffix_036, ridgeSupport648_suffix_037, ridgeSupport648_suffix_038, ridgeSupport648_suffix_039, ridgeSupport648_suffix_040, ridgeSupport648_suffix_041, ridgeSupport648_suffix_042, ridgeSupport648_suffix_043, ridgeSupport648_suffix_044, ridgeSupport648_suffix_045, ridgeSupport648_suffix_046, ridgeSupport648_suffix_047, ridgeSupport648_suffix_048, ridgeSupport648_suffix_049, ridgeSupport648_suffix_050, ridgeSupport648_suffix_051, ridgeSupport648_suffix_052, ridgeSupport648_suffix_053, ridgeSupport648_suffix_054, ridgeSupport648_suffix_055, ridgeSupport648_suffix_056, ridgeSupport648_suffix_057, ridgeSupport648_suffix_058, ridgeSupport648_suffix_059, ridgeSupport648_suffix_060, List.all_append, List.all_nil, ridgeSupport648_000_checked, ridgeSupport648_001_checked, ridgeSupport648_002_checked, ridgeSupport648_003_checked, ridgeSupport648_004_checked, ridgeSupport648_005_checked, ridgeSupport648_006_checked, ridgeSupport648_007_checked, ridgeSupport648_008_checked, ridgeSupport648_009_checked, ridgeSupport648_010_checked, ridgeSupport648_011_checked, ridgeSupport648_012_checked, ridgeSupport648_013_checked, ridgeSupport648_014_checked, ridgeSupport648_015_checked, ridgeSupport648_016_checked, ridgeSupport648_017_checked, ridgeSupport648_018_checked, ridgeSupport648_019_checked, ridgeSupport648_020_checked, ridgeSupport648_021_checked, ridgeSupport648_022_checked, ridgeSupport648_023_checked, ridgeSupport648_024_checked, ridgeSupport648_025_checked, ridgeSupport648_026_checked, ridgeSupport648_027_checked, ridgeSupport648_028_checked, ridgeSupport648_029_checked, ridgeSupport648_030_checked, ridgeSupport648_031_checked, ridgeSupport648_032_checked, ridgeSupport648_033_checked, ridgeSupport648_034_checked, ridgeSupport648_035_checked, ridgeSupport648_036_checked, ridgeSupport648_037_checked, ridgeSupport648_038_checked, ridgeSupport648_039_checked, ridgeSupport648_040_checked, ridgeSupport648_041_checked, ridgeSupport648_042_checked, ridgeSupport648_043_checked, ridgeSupport648_044_checked, ridgeSupport648_045_checked, ridgeSupport648_046_checked, ridgeSupport648_047_checked, ridgeSupport648_048_checked, ridgeSupport648_049_checked, ridgeSupport648_050_checked, ridgeSupport648_051_checked, ridgeSupport648_052_checked, ridgeSupport648_053_checked, ridgeSupport648_054_checked, ridgeSupport648_055_checked, ridgeSupport648_056_checked, ridgeSupport648_057_checked, ridgeSupport648_058_checked, ridgeSupport648_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
