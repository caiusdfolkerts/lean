module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport769Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 769 036 15
cert_ridgeSupport_suffix_decode_2 769 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 769 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 769 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 769 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 769 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 769 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 769 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 769 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 769 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 769 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 769 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 769 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 769 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 769 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 769 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 769 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 769 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 769 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 769 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 769 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 769 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 769 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 769 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 769 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 769 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 769 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 769 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 769 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 769 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 769 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 769 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 769 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 769 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 769 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 769 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 769 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 769
theorem ridgeTest_large_769 : ridgeTest 769 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport769_eq]
    simp only [ridgeSupport769_suffix_000, ridgeSupport769_suffix_001, ridgeSupport769_suffix_002, ridgeSupport769_suffix_003, ridgeSupport769_suffix_004, ridgeSupport769_suffix_005, ridgeSupport769_suffix_006, ridgeSupport769_suffix_007, ridgeSupport769_suffix_008, ridgeSupport769_suffix_009, ridgeSupport769_suffix_010, ridgeSupport769_suffix_011, ridgeSupport769_suffix_012, ridgeSupport769_suffix_013, ridgeSupport769_suffix_014, ridgeSupport769_suffix_015, ridgeSupport769_suffix_016, ridgeSupport769_suffix_017, ridgeSupport769_suffix_018, ridgeSupport769_suffix_019, ridgeSupport769_suffix_020, ridgeSupport769_suffix_021, ridgeSupport769_suffix_022, ridgeSupport769_suffix_023, ridgeSupport769_suffix_024, ridgeSupport769_suffix_025, ridgeSupport769_suffix_026, ridgeSupport769_suffix_027, ridgeSupport769_suffix_028, ridgeSupport769_suffix_029, ridgeSupport769_suffix_030, ridgeSupport769_suffix_031, ridgeSupport769_suffix_032, ridgeSupport769_suffix_033, ridgeSupport769_suffix_034, ridgeSupport769_suffix_035, ridgeSupport769_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport769_000_mask, ridgeSupport769_001_mask, ridgeSupport769_002_mask, ridgeSupport769_003_mask, ridgeSupport769_004_mask, ridgeSupport769_005_mask, ridgeSupport769_006_mask, ridgeSupport769_007_mask, ridgeSupport769_008_mask, ridgeSupport769_009_mask, ridgeSupport769_010_mask, ridgeSupport769_011_mask, ridgeSupport769_012_mask, ridgeSupport769_013_mask, ridgeSupport769_014_mask, ridgeSupport769_015_mask, ridgeSupport769_016_mask, ridgeSupport769_017_mask, ridgeSupport769_018_mask, ridgeSupport769_019_mask, ridgeSupport769_020_mask, ridgeSupport769_021_mask, ridgeSupport769_022_mask, ridgeSupport769_023_mask, ridgeSupport769_024_mask, ridgeSupport769_025_mask, ridgeSupport769_026_mask, ridgeSupport769_027_mask, ridgeSupport769_028_mask, ridgeSupport769_029_mask, ridgeSupport769_030_mask, ridgeSupport769_031_mask, ridgeSupport769_032_mask, ridgeSupport769_033_mask, ridgeSupport769_034_mask, ridgeSupport769_035_mask]
    decide +kernel
  · rw [ridgeSupport769_eq]
    simp only [ridgeSupport769_suffix_000, ridgeSupport769_suffix_001, ridgeSupport769_suffix_002, ridgeSupport769_suffix_003, ridgeSupport769_suffix_004, ridgeSupport769_suffix_005, ridgeSupport769_suffix_006, ridgeSupport769_suffix_007, ridgeSupport769_suffix_008, ridgeSupport769_suffix_009, ridgeSupport769_suffix_010, ridgeSupport769_suffix_011, ridgeSupport769_suffix_012, ridgeSupport769_suffix_013, ridgeSupport769_suffix_014, ridgeSupport769_suffix_015, ridgeSupport769_suffix_016, ridgeSupport769_suffix_017, ridgeSupport769_suffix_018, ridgeSupport769_suffix_019, ridgeSupport769_suffix_020, ridgeSupport769_suffix_021, ridgeSupport769_suffix_022, ridgeSupport769_suffix_023, ridgeSupport769_suffix_024, ridgeSupport769_suffix_025, ridgeSupport769_suffix_026, ridgeSupport769_suffix_027, ridgeSupport769_suffix_028, ridgeSupport769_suffix_029, ridgeSupport769_suffix_030, ridgeSupport769_suffix_031, ridgeSupport769_suffix_032, ridgeSupport769_suffix_033, ridgeSupport769_suffix_034, ridgeSupport769_suffix_035, ridgeSupport769_suffix_036, List.all_append, List.all_nil, ridgeSupport769_000_checked, ridgeSupport769_001_checked, ridgeSupport769_002_checked, ridgeSupport769_003_checked, ridgeSupport769_004_checked, ridgeSupport769_005_checked, ridgeSupport769_006_checked, ridgeSupport769_007_checked, ridgeSupport769_008_checked, ridgeSupport769_009_checked, ridgeSupport769_010_checked, ridgeSupport769_011_checked, ridgeSupport769_012_checked, ridgeSupport769_013_checked, ridgeSupport769_014_checked, ridgeSupport769_015_checked, ridgeSupport769_016_checked, ridgeSupport769_017_checked, ridgeSupport769_018_checked, ridgeSupport769_019_checked, ridgeSupport769_020_checked, ridgeSupport769_021_checked, ridgeSupport769_022_checked, ridgeSupport769_023_checked, ridgeSupport769_024_checked, ridgeSupport769_025_checked, ridgeSupport769_026_checked, ridgeSupport769_027_checked, ridgeSupport769_028_checked, ridgeSupport769_029_checked, ridgeSupport769_030_checked, ridgeSupport769_031_checked, ridgeSupport769_032_checked, ridgeSupport769_033_checked, ridgeSupport769_034_checked, ridgeSupport769_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
