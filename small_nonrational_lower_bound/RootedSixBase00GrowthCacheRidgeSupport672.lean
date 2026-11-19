module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport672Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 672 036 15
cert_ridgeSupport_suffix_decode_2 672 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 672 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 672 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 672 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 672 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 672 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 672 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 672 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 672 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 672 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 672 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 672 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 672 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 672 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 672 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 672 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 672 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 672 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 672 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 672 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 672 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 672 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 672 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 672 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 672 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 672 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 672 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 672 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 672 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 672 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 672 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 672 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 672 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 672 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 672 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 672 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 672
theorem ridgeTest_large_672 : ridgeTest 672 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, ridgeSupport672_suffix_011, ridgeSupport672_suffix_012, ridgeSupport672_suffix_013, ridgeSupport672_suffix_014, ridgeSupport672_suffix_015, ridgeSupport672_suffix_016, ridgeSupport672_suffix_017, ridgeSupport672_suffix_018, ridgeSupport672_suffix_019, ridgeSupport672_suffix_020, ridgeSupport672_suffix_021, ridgeSupport672_suffix_022, ridgeSupport672_suffix_023, ridgeSupport672_suffix_024, ridgeSupport672_suffix_025, ridgeSupport672_suffix_026, ridgeSupport672_suffix_027, ridgeSupport672_suffix_028, ridgeSupport672_suffix_029, ridgeSupport672_suffix_030, ridgeSupport672_suffix_031, ridgeSupport672_suffix_032, ridgeSupport672_suffix_033, ridgeSupport672_suffix_034, ridgeSupport672_suffix_035, ridgeSupport672_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport672_000_mask, ridgeSupport672_001_mask, ridgeSupport672_002_mask, ridgeSupport672_003_mask, ridgeSupport672_004_mask, ridgeSupport672_005_mask, ridgeSupport672_006_mask, ridgeSupport672_007_mask, ridgeSupport672_008_mask, ridgeSupport672_009_mask, ridgeSupport672_010_mask, ridgeSupport672_011_mask, ridgeSupport672_012_mask, ridgeSupport672_013_mask, ridgeSupport672_014_mask, ridgeSupport672_015_mask, ridgeSupport672_016_mask, ridgeSupport672_017_mask, ridgeSupport672_018_mask, ridgeSupport672_019_mask, ridgeSupport672_020_mask, ridgeSupport672_021_mask, ridgeSupport672_022_mask, ridgeSupport672_023_mask, ridgeSupport672_024_mask, ridgeSupport672_025_mask, ridgeSupport672_026_mask, ridgeSupport672_027_mask, ridgeSupport672_028_mask, ridgeSupport672_029_mask, ridgeSupport672_030_mask, ridgeSupport672_031_mask, ridgeSupport672_032_mask, ridgeSupport672_033_mask, ridgeSupport672_034_mask, ridgeSupport672_035_mask]
    decide +kernel
  · rw [ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, ridgeSupport672_suffix_011, ridgeSupport672_suffix_012, ridgeSupport672_suffix_013, ridgeSupport672_suffix_014, ridgeSupport672_suffix_015, ridgeSupport672_suffix_016, ridgeSupport672_suffix_017, ridgeSupport672_suffix_018, ridgeSupport672_suffix_019, ridgeSupport672_suffix_020, ridgeSupport672_suffix_021, ridgeSupport672_suffix_022, ridgeSupport672_suffix_023, ridgeSupport672_suffix_024, ridgeSupport672_suffix_025, ridgeSupport672_suffix_026, ridgeSupport672_suffix_027, ridgeSupport672_suffix_028, ridgeSupport672_suffix_029, ridgeSupport672_suffix_030, ridgeSupport672_suffix_031, ridgeSupport672_suffix_032, ridgeSupport672_suffix_033, ridgeSupport672_suffix_034, ridgeSupport672_suffix_035, ridgeSupport672_suffix_036, List.all_append, List.all_nil, ridgeSupport672_000_checked, ridgeSupport672_001_checked, ridgeSupport672_002_checked, ridgeSupport672_003_checked, ridgeSupport672_004_checked, ridgeSupport672_005_checked, ridgeSupport672_006_checked, ridgeSupport672_007_checked, ridgeSupport672_008_checked, ridgeSupport672_009_checked, ridgeSupport672_010_checked, ridgeSupport672_011_checked, ridgeSupport672_012_checked, ridgeSupport672_013_checked, ridgeSupport672_014_checked, ridgeSupport672_015_checked, ridgeSupport672_016_checked, ridgeSupport672_017_checked, ridgeSupport672_018_checked, ridgeSupport672_019_checked, ridgeSupport672_020_checked, ridgeSupport672_021_checked, ridgeSupport672_022_checked, ridgeSupport672_023_checked, ridgeSupport672_024_checked, ridgeSupport672_025_checked, ridgeSupport672_026_checked, ridgeSupport672_027_checked, ridgeSupport672_028_checked, ridgeSupport672_029_checked, ridgeSupport672_030_checked, ridgeSupport672_031_checked, ridgeSupport672_032_checked, ridgeSupport672_033_checked, ridgeSupport672_034_checked, ridgeSupport672_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
