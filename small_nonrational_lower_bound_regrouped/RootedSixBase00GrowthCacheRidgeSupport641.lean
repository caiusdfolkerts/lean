module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport641Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 641 036 15
cert_ridgeSupport_suffix_decode_2 641 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 641 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 641 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 641 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 641 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 641 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 641 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 641 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 641 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 641 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 641 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 641 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 641 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 641 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 641 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 641 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 641 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 641 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 641 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 641 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 641 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 641 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 641 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 641 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 641 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 641 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 641 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 641 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 641 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 641 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 641 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 641 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 641 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 641 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 641 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 641 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 641
theorem ridgeTest_large_641 : ridgeTest 641 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport641_eq]
    simp only [ridgeSupport641_suffix_000, ridgeSupport641_suffix_001, ridgeSupport641_suffix_002, ridgeSupport641_suffix_003, ridgeSupport641_suffix_004, ridgeSupport641_suffix_005, ridgeSupport641_suffix_006, ridgeSupport641_suffix_007, ridgeSupport641_suffix_008, ridgeSupport641_suffix_009, ridgeSupport641_suffix_010, ridgeSupport641_suffix_011, ridgeSupport641_suffix_012, ridgeSupport641_suffix_013, ridgeSupport641_suffix_014, ridgeSupport641_suffix_015, ridgeSupport641_suffix_016, ridgeSupport641_suffix_017, ridgeSupport641_suffix_018, ridgeSupport641_suffix_019, ridgeSupport641_suffix_020, ridgeSupport641_suffix_021, ridgeSupport641_suffix_022, ridgeSupport641_suffix_023, ridgeSupport641_suffix_024, ridgeSupport641_suffix_025, ridgeSupport641_suffix_026, ridgeSupport641_suffix_027, ridgeSupport641_suffix_028, ridgeSupport641_suffix_029, ridgeSupport641_suffix_030, ridgeSupport641_suffix_031, ridgeSupport641_suffix_032, ridgeSupport641_suffix_033, ridgeSupport641_suffix_034, ridgeSupport641_suffix_035, ridgeSupport641_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport641_000_mask, ridgeSupport641_001_mask, ridgeSupport641_002_mask, ridgeSupport641_003_mask, ridgeSupport641_004_mask, ridgeSupport641_005_mask, ridgeSupport641_006_mask, ridgeSupport641_007_mask, ridgeSupport641_008_mask, ridgeSupport641_009_mask, ridgeSupport641_010_mask, ridgeSupport641_011_mask, ridgeSupport641_012_mask, ridgeSupport641_013_mask, ridgeSupport641_014_mask, ridgeSupport641_015_mask, ridgeSupport641_016_mask, ridgeSupport641_017_mask, ridgeSupport641_018_mask, ridgeSupport641_019_mask, ridgeSupport641_020_mask, ridgeSupport641_021_mask, ridgeSupport641_022_mask, ridgeSupport641_023_mask, ridgeSupport641_024_mask, ridgeSupport641_025_mask, ridgeSupport641_026_mask, ridgeSupport641_027_mask, ridgeSupport641_028_mask, ridgeSupport641_029_mask, ridgeSupport641_030_mask, ridgeSupport641_031_mask, ridgeSupport641_032_mask, ridgeSupport641_033_mask, ridgeSupport641_034_mask, ridgeSupport641_035_mask]
    decide +kernel
  · rw [ridgeSupport641_eq]
    simp only [ridgeSupport641_suffix_000, ridgeSupport641_suffix_001, ridgeSupport641_suffix_002, ridgeSupport641_suffix_003, ridgeSupport641_suffix_004, ridgeSupport641_suffix_005, ridgeSupport641_suffix_006, ridgeSupport641_suffix_007, ridgeSupport641_suffix_008, ridgeSupport641_suffix_009, ridgeSupport641_suffix_010, ridgeSupport641_suffix_011, ridgeSupport641_suffix_012, ridgeSupport641_suffix_013, ridgeSupport641_suffix_014, ridgeSupport641_suffix_015, ridgeSupport641_suffix_016, ridgeSupport641_suffix_017, ridgeSupport641_suffix_018, ridgeSupport641_suffix_019, ridgeSupport641_suffix_020, ridgeSupport641_suffix_021, ridgeSupport641_suffix_022, ridgeSupport641_suffix_023, ridgeSupport641_suffix_024, ridgeSupport641_suffix_025, ridgeSupport641_suffix_026, ridgeSupport641_suffix_027, ridgeSupport641_suffix_028, ridgeSupport641_suffix_029, ridgeSupport641_suffix_030, ridgeSupport641_suffix_031, ridgeSupport641_suffix_032, ridgeSupport641_suffix_033, ridgeSupport641_suffix_034, ridgeSupport641_suffix_035, ridgeSupport641_suffix_036, List.all_append, List.all_nil, ridgeSupport641_000_checked, ridgeSupport641_001_checked, ridgeSupport641_002_checked, ridgeSupport641_003_checked, ridgeSupport641_004_checked, ridgeSupport641_005_checked, ridgeSupport641_006_checked, ridgeSupport641_007_checked, ridgeSupport641_008_checked, ridgeSupport641_009_checked, ridgeSupport641_010_checked, ridgeSupport641_011_checked, ridgeSupport641_012_checked, ridgeSupport641_013_checked, ridgeSupport641_014_checked, ridgeSupport641_015_checked, ridgeSupport641_016_checked, ridgeSupport641_017_checked, ridgeSupport641_018_checked, ridgeSupport641_019_checked, ridgeSupport641_020_checked, ridgeSupport641_021_checked, ridgeSupport641_022_checked, ridgeSupport641_023_checked, ridgeSupport641_024_checked, ridgeSupport641_025_checked, ridgeSupport641_026_checked, ridgeSupport641_027_checked, ridgeSupport641_028_checked, ridgeSupport641_029_checked, ridgeSupport641_030_checked, ridgeSupport641_031_checked, ridgeSupport641_032_checked, ridgeSupport641_033_checked, ridgeSupport641_034_checked, ridgeSupport641_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
