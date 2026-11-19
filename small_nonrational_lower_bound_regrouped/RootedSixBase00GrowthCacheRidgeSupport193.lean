module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport193Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 193 036 15
cert_ridgeSupport_suffix_decode_2 193 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 193 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 193 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 193 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 193 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 193 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 193 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 193 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 193 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 193 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 193 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 193 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 193 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 193 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 193 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 193 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 193 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 193 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 193 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 193 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 193 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 193 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 193 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 193 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 193 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 193 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 193 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 193 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 193 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 193 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 193 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 193 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 193 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 193 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 193 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 193 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 193
theorem ridgeTest_large_193 : ridgeTest 193 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport193_eq]
    simp only [ridgeSupport193_suffix_000, ridgeSupport193_suffix_001, ridgeSupport193_suffix_002, ridgeSupport193_suffix_003, ridgeSupport193_suffix_004, ridgeSupport193_suffix_005, ridgeSupport193_suffix_006, ridgeSupport193_suffix_007, ridgeSupport193_suffix_008, ridgeSupport193_suffix_009, ridgeSupport193_suffix_010, ridgeSupport193_suffix_011, ridgeSupport193_suffix_012, ridgeSupport193_suffix_013, ridgeSupport193_suffix_014, ridgeSupport193_suffix_015, ridgeSupport193_suffix_016, ridgeSupport193_suffix_017, ridgeSupport193_suffix_018, ridgeSupport193_suffix_019, ridgeSupport193_suffix_020, ridgeSupport193_suffix_021, ridgeSupport193_suffix_022, ridgeSupport193_suffix_023, ridgeSupport193_suffix_024, ridgeSupport193_suffix_025, ridgeSupport193_suffix_026, ridgeSupport193_suffix_027, ridgeSupport193_suffix_028, ridgeSupport193_suffix_029, ridgeSupport193_suffix_030, ridgeSupport193_suffix_031, ridgeSupport193_suffix_032, ridgeSupport193_suffix_033, ridgeSupport193_suffix_034, ridgeSupport193_suffix_035, ridgeSupport193_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport193_000_mask, ridgeSupport193_001_mask, ridgeSupport193_002_mask, ridgeSupport193_003_mask, ridgeSupport193_004_mask, ridgeSupport193_005_mask, ridgeSupport193_006_mask, ridgeSupport193_007_mask, ridgeSupport193_008_mask, ridgeSupport193_009_mask, ridgeSupport193_010_mask, ridgeSupport193_011_mask, ridgeSupport193_012_mask, ridgeSupport193_013_mask, ridgeSupport193_014_mask, ridgeSupport193_015_mask, ridgeSupport193_016_mask, ridgeSupport193_017_mask, ridgeSupport193_018_mask, ridgeSupport193_019_mask, ridgeSupport193_020_mask, ridgeSupport193_021_mask, ridgeSupport193_022_mask, ridgeSupport193_023_mask, ridgeSupport193_024_mask, ridgeSupport193_025_mask, ridgeSupport193_026_mask, ridgeSupport193_027_mask, ridgeSupport193_028_mask, ridgeSupport193_029_mask, ridgeSupport193_030_mask, ridgeSupport193_031_mask, ridgeSupport193_032_mask, ridgeSupport193_033_mask, ridgeSupport193_034_mask, ridgeSupport193_035_mask]
    decide +kernel
  · rw [ridgeSupport193_eq]
    simp only [ridgeSupport193_suffix_000, ridgeSupport193_suffix_001, ridgeSupport193_suffix_002, ridgeSupport193_suffix_003, ridgeSupport193_suffix_004, ridgeSupport193_suffix_005, ridgeSupport193_suffix_006, ridgeSupport193_suffix_007, ridgeSupport193_suffix_008, ridgeSupport193_suffix_009, ridgeSupport193_suffix_010, ridgeSupport193_suffix_011, ridgeSupport193_suffix_012, ridgeSupport193_suffix_013, ridgeSupport193_suffix_014, ridgeSupport193_suffix_015, ridgeSupport193_suffix_016, ridgeSupport193_suffix_017, ridgeSupport193_suffix_018, ridgeSupport193_suffix_019, ridgeSupport193_suffix_020, ridgeSupport193_suffix_021, ridgeSupport193_suffix_022, ridgeSupport193_suffix_023, ridgeSupport193_suffix_024, ridgeSupport193_suffix_025, ridgeSupport193_suffix_026, ridgeSupport193_suffix_027, ridgeSupport193_suffix_028, ridgeSupport193_suffix_029, ridgeSupport193_suffix_030, ridgeSupport193_suffix_031, ridgeSupport193_suffix_032, ridgeSupport193_suffix_033, ridgeSupport193_suffix_034, ridgeSupport193_suffix_035, ridgeSupport193_suffix_036, List.all_append, List.all_nil, ridgeSupport193_000_checked, ridgeSupport193_001_checked, ridgeSupport193_002_checked, ridgeSupport193_003_checked, ridgeSupport193_004_checked, ridgeSupport193_005_checked, ridgeSupport193_006_checked, ridgeSupport193_007_checked, ridgeSupport193_008_checked, ridgeSupport193_009_checked, ridgeSupport193_010_checked, ridgeSupport193_011_checked, ridgeSupport193_012_checked, ridgeSupport193_013_checked, ridgeSupport193_014_checked, ridgeSupport193_015_checked, ridgeSupport193_016_checked, ridgeSupport193_017_checked, ridgeSupport193_018_checked, ridgeSupport193_019_checked, ridgeSupport193_020_checked, ridgeSupport193_021_checked, ridgeSupport193_022_checked, ridgeSupport193_023_checked, ridgeSupport193_024_checked, ridgeSupport193_025_checked, ridgeSupport193_026_checked, ridgeSupport193_027_checked, ridgeSupport193_028_checked, ridgeSupport193_029_checked, ridgeSupport193_030_checked, ridgeSupport193_031_checked, ridgeSupport193_032_checked, ridgeSupport193_033_checked, ridgeSupport193_034_checked, ridgeSupport193_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
