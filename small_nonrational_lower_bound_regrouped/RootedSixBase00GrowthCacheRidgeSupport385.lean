module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport385Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 385 036 15
cert_ridgeSupport_suffix_decode_2 385 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 385 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 385 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 385 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 385 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 385 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 385 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 385 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 385 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 385 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 385 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 385 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 385 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 385 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 385 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 385 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 385 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 385 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 385 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 385 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 385 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 385 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 385 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 385 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 385 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 385 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 385 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 385 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 385 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 385 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 385 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 385 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 385 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 385 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 385 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 385 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 385
theorem ridgeTest_large_385 : ridgeTest 385 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport385_eq]
    simp only [ridgeSupport385_suffix_000, ridgeSupport385_suffix_001, ridgeSupport385_suffix_002, ridgeSupport385_suffix_003, ridgeSupport385_suffix_004, ridgeSupport385_suffix_005, ridgeSupport385_suffix_006, ridgeSupport385_suffix_007, ridgeSupport385_suffix_008, ridgeSupport385_suffix_009, ridgeSupport385_suffix_010, ridgeSupport385_suffix_011, ridgeSupport385_suffix_012, ridgeSupport385_suffix_013, ridgeSupport385_suffix_014, ridgeSupport385_suffix_015, ridgeSupport385_suffix_016, ridgeSupport385_suffix_017, ridgeSupport385_suffix_018, ridgeSupport385_suffix_019, ridgeSupport385_suffix_020, ridgeSupport385_suffix_021, ridgeSupport385_suffix_022, ridgeSupport385_suffix_023, ridgeSupport385_suffix_024, ridgeSupport385_suffix_025, ridgeSupport385_suffix_026, ridgeSupport385_suffix_027, ridgeSupport385_suffix_028, ridgeSupport385_suffix_029, ridgeSupport385_suffix_030, ridgeSupport385_suffix_031, ridgeSupport385_suffix_032, ridgeSupport385_suffix_033, ridgeSupport385_suffix_034, ridgeSupport385_suffix_035, ridgeSupport385_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport385_000_mask, ridgeSupport385_001_mask, ridgeSupport385_002_mask, ridgeSupport385_003_mask, ridgeSupport385_004_mask, ridgeSupport385_005_mask, ridgeSupport385_006_mask, ridgeSupport385_007_mask, ridgeSupport385_008_mask, ridgeSupport385_009_mask, ridgeSupport385_010_mask, ridgeSupport385_011_mask, ridgeSupport385_012_mask, ridgeSupport385_013_mask, ridgeSupport385_014_mask, ridgeSupport385_015_mask, ridgeSupport385_016_mask, ridgeSupport385_017_mask, ridgeSupport385_018_mask, ridgeSupport385_019_mask, ridgeSupport385_020_mask, ridgeSupport385_021_mask, ridgeSupport385_022_mask, ridgeSupport385_023_mask, ridgeSupport385_024_mask, ridgeSupport385_025_mask, ridgeSupport385_026_mask, ridgeSupport385_027_mask, ridgeSupport385_028_mask, ridgeSupport385_029_mask, ridgeSupport385_030_mask, ridgeSupport385_031_mask, ridgeSupport385_032_mask, ridgeSupport385_033_mask, ridgeSupport385_034_mask, ridgeSupport385_035_mask]
    decide +kernel
  · rw [ridgeSupport385_eq]
    simp only [ridgeSupport385_suffix_000, ridgeSupport385_suffix_001, ridgeSupport385_suffix_002, ridgeSupport385_suffix_003, ridgeSupport385_suffix_004, ridgeSupport385_suffix_005, ridgeSupport385_suffix_006, ridgeSupport385_suffix_007, ridgeSupport385_suffix_008, ridgeSupport385_suffix_009, ridgeSupport385_suffix_010, ridgeSupport385_suffix_011, ridgeSupport385_suffix_012, ridgeSupport385_suffix_013, ridgeSupport385_suffix_014, ridgeSupport385_suffix_015, ridgeSupport385_suffix_016, ridgeSupport385_suffix_017, ridgeSupport385_suffix_018, ridgeSupport385_suffix_019, ridgeSupport385_suffix_020, ridgeSupport385_suffix_021, ridgeSupport385_suffix_022, ridgeSupport385_suffix_023, ridgeSupport385_suffix_024, ridgeSupport385_suffix_025, ridgeSupport385_suffix_026, ridgeSupport385_suffix_027, ridgeSupport385_suffix_028, ridgeSupport385_suffix_029, ridgeSupport385_suffix_030, ridgeSupport385_suffix_031, ridgeSupport385_suffix_032, ridgeSupport385_suffix_033, ridgeSupport385_suffix_034, ridgeSupport385_suffix_035, ridgeSupport385_suffix_036, List.all_append, List.all_nil, ridgeSupport385_000_checked, ridgeSupport385_001_checked, ridgeSupport385_002_checked, ridgeSupport385_003_checked, ridgeSupport385_004_checked, ridgeSupport385_005_checked, ridgeSupport385_006_checked, ridgeSupport385_007_checked, ridgeSupport385_008_checked, ridgeSupport385_009_checked, ridgeSupport385_010_checked, ridgeSupport385_011_checked, ridgeSupport385_012_checked, ridgeSupport385_013_checked, ridgeSupport385_014_checked, ridgeSupport385_015_checked, ridgeSupport385_016_checked, ridgeSupport385_017_checked, ridgeSupport385_018_checked, ridgeSupport385_019_checked, ridgeSupport385_020_checked, ridgeSupport385_021_checked, ridgeSupport385_022_checked, ridgeSupport385_023_checked, ridgeSupport385_024_checked, ridgeSupport385_025_checked, ridgeSupport385_026_checked, ridgeSupport385_027_checked, ridgeSupport385_028_checked, ridgeSupport385_029_checked, ridgeSupport385_030_checked, ridgeSupport385_031_checked, ridgeSupport385_032_checked, ridgeSupport385_033_checked, ridgeSupport385_034_checked, ridgeSupport385_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
