module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport608Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 608 036 15
cert_ridgeSupport_suffix_decode_2 608 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 608 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 608 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 608 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 608 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 608 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 608 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 608 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 608 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 608 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 608 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 608 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 608 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 608 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 608 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 608 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 608 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 608 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 608 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 608 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 608 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 608 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 608 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 608 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 608 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 608 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 608 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 608 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 608 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 608 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 608 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 608 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 608 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 608 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 608 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 608 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 608
theorem ridgeTest_large_608 : ridgeTest 608 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, ridgeSupport608_suffix_011, ridgeSupport608_suffix_012, ridgeSupport608_suffix_013, ridgeSupport608_suffix_014, ridgeSupport608_suffix_015, ridgeSupport608_suffix_016, ridgeSupport608_suffix_017, ridgeSupport608_suffix_018, ridgeSupport608_suffix_019, ridgeSupport608_suffix_020, ridgeSupport608_suffix_021, ridgeSupport608_suffix_022, ridgeSupport608_suffix_023, ridgeSupport608_suffix_024, ridgeSupport608_suffix_025, ridgeSupport608_suffix_026, ridgeSupport608_suffix_027, ridgeSupport608_suffix_028, ridgeSupport608_suffix_029, ridgeSupport608_suffix_030, ridgeSupport608_suffix_031, ridgeSupport608_suffix_032, ridgeSupport608_suffix_033, ridgeSupport608_suffix_034, ridgeSupport608_suffix_035, ridgeSupport608_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport608_000_mask, ridgeSupport608_001_mask, ridgeSupport608_002_mask, ridgeSupport608_003_mask, ridgeSupport608_004_mask, ridgeSupport608_005_mask, ridgeSupport608_006_mask, ridgeSupport608_007_mask, ridgeSupport608_008_mask, ridgeSupport608_009_mask, ridgeSupport608_010_mask, ridgeSupport608_011_mask, ridgeSupport608_012_mask, ridgeSupport608_013_mask, ridgeSupport608_014_mask, ridgeSupport608_015_mask, ridgeSupport608_016_mask, ridgeSupport608_017_mask, ridgeSupport608_018_mask, ridgeSupport608_019_mask, ridgeSupport608_020_mask, ridgeSupport608_021_mask, ridgeSupport608_022_mask, ridgeSupport608_023_mask, ridgeSupport608_024_mask, ridgeSupport608_025_mask, ridgeSupport608_026_mask, ridgeSupport608_027_mask, ridgeSupport608_028_mask, ridgeSupport608_029_mask, ridgeSupport608_030_mask, ridgeSupport608_031_mask, ridgeSupport608_032_mask, ridgeSupport608_033_mask, ridgeSupport608_034_mask, ridgeSupport608_035_mask]
    decide +kernel
  · rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, ridgeSupport608_suffix_011, ridgeSupport608_suffix_012, ridgeSupport608_suffix_013, ridgeSupport608_suffix_014, ridgeSupport608_suffix_015, ridgeSupport608_suffix_016, ridgeSupport608_suffix_017, ridgeSupport608_suffix_018, ridgeSupport608_suffix_019, ridgeSupport608_suffix_020, ridgeSupport608_suffix_021, ridgeSupport608_suffix_022, ridgeSupport608_suffix_023, ridgeSupport608_suffix_024, ridgeSupport608_suffix_025, ridgeSupport608_suffix_026, ridgeSupport608_suffix_027, ridgeSupport608_suffix_028, ridgeSupport608_suffix_029, ridgeSupport608_suffix_030, ridgeSupport608_suffix_031, ridgeSupport608_suffix_032, ridgeSupport608_suffix_033, ridgeSupport608_suffix_034, ridgeSupport608_suffix_035, ridgeSupport608_suffix_036, List.all_append, List.all_nil, ridgeSupport608_000_checked, ridgeSupport608_001_checked, ridgeSupport608_002_checked, ridgeSupport608_003_checked, ridgeSupport608_004_checked, ridgeSupport608_005_checked, ridgeSupport608_006_checked, ridgeSupport608_007_checked, ridgeSupport608_008_checked, ridgeSupport608_009_checked, ridgeSupport608_010_checked, ridgeSupport608_011_checked, ridgeSupport608_012_checked, ridgeSupport608_013_checked, ridgeSupport608_014_checked, ridgeSupport608_015_checked, ridgeSupport608_016_checked, ridgeSupport608_017_checked, ridgeSupport608_018_checked, ridgeSupport608_019_checked, ridgeSupport608_020_checked, ridgeSupport608_021_checked, ridgeSupport608_022_checked, ridgeSupport608_023_checked, ridgeSupport608_024_checked, ridgeSupport608_025_checked, ridgeSupport608_026_checked, ridgeSupport608_027_checked, ridgeSupport608_028_checked, ridgeSupport608_029_checked, ridgeSupport608_030_checked, ridgeSupport608_031_checked, ridgeSupport608_032_checked, ridgeSupport608_033_checked, ridgeSupport608_034_checked, ridgeSupport608_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
