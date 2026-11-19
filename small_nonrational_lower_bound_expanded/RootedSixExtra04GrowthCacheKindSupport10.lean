module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra04GrowthCacheKindSupport10Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 10 036 12
cert_kindSupport_suffix_decode_6 10 035 12 32 32 036 036 0
cert_kindSupport_suffix_decode_6 10 034 12 64 32 036 035 32
cert_kindSupport_suffix_decode_6 10 033 12 96 32 036 034 64
cert_kindSupport_suffix_decode_6 10 032 12 128 32 036 033 96
cert_kindSupport_suffix_decode_6 10 031 12 160 32 036 032 128
cert_kindSupport_suffix_decode_6 10 030 12 192 32 036 031 160
cert_kindSupport_suffix_decode_6 10 029 12 224 32 036 030 192
cert_kindSupport_suffix_decode_6 10 028 12 256 32 036 029 224
cert_kindSupport_suffix_decode_6 10 027 12 288 32 036 028 256
cert_kindSupport_suffix_decode_6 10 026 12 320 32 036 027 288
cert_kindSupport_suffix_decode_6 10 025 12 352 32 036 026 320
cert_kindSupport_suffix_decode_6 10 024 12 384 32 036 025 352
cert_kindSupport_suffix_decode_6 10 023 12 416 32 036 024 384
cert_kindSupport_suffix_decode_6 10 022 12 448 32 036 023 416
cert_kindSupport_suffix_decode_6 10 021 12 480 32 036 022 448
cert_kindSupport_suffix_decode_6 10 020 12 512 32 036 021 480
cert_kindSupport_suffix_decode_6 10 019 12 544 32 036 020 512
cert_kindSupport_suffix_decode_6 10 018 12 576 32 036 019 544
cert_kindSupport_suffix_decode_6 10 017 12 608 32 036 018 576
cert_kindSupport_suffix_decode_6 10 016 12 640 32 036 017 608
cert_kindSupport_suffix_decode_6 10 015 12 672 32 036 016 640
cert_kindSupport_suffix_decode_6 10 014 12 704 32 036 015 672
cert_kindSupport_suffix_decode_6 10 013 12 736 32 036 014 704
cert_kindSupport_suffix_decode_6 10 012 12 768 32 036 013 736
cert_kindSupport_suffix_decode_6 10 011 12 800 32 036 012 768
cert_kindSupport_suffix_decode_6 10 010 12 832 32 036 011 800
cert_kindSupport_suffix_decode_6 10 009 12 864 32 036 010 832
cert_kindSupport_suffix_decode_6 10 008 12 896 32 036 009 864
cert_kindSupport_suffix_decode_6 10 007 12 928 32 036 008 896
cert_kindSupport_suffix_decode_6 10 006 12 960 32 036 007 928
cert_kindSupport_suffix_decode_6 10 005 12 992 32 036 006 960
cert_kindSupport_suffix_decode_6 10 004 12 1024 32 036 005 992
cert_kindSupport_suffix_decode_6 10 003 12 1056 32 036 004 1024
cert_kindSupport_suffix_decode_6 10 002 12 1088 32 036 003 1056
cert_kindSupport_suffix_decode_6 10 001 12 1120 32 036 002 1088
cert_kindSupport_suffix_decode_6 10 000 12 1152 32 036 001 1120
cert_kindSupport_eq_3 10
theorem kindTest_large_10 : kindTest 10 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, kindSupport10_suffix_025, kindSupport10_suffix_026, kindSupport10_suffix_027, kindSupport10_suffix_028, kindSupport10_suffix_029, kindSupport10_suffix_030, kindSupport10_suffix_031, kindSupport10_suffix_032, kindSupport10_suffix_033, kindSupport10_suffix_034, kindSupport10_suffix_035, kindSupport10_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport10_000_mask, kindSupport10_001_mask, kindSupport10_002_mask, kindSupport10_003_mask, kindSupport10_004_mask, kindSupport10_005_mask, kindSupport10_006_mask, kindSupport10_007_mask, kindSupport10_008_mask, kindSupport10_009_mask, kindSupport10_010_mask, kindSupport10_011_mask, kindSupport10_012_mask, kindSupport10_013_mask, kindSupport10_014_mask, kindSupport10_015_mask, kindSupport10_016_mask, kindSupport10_017_mask, kindSupport10_018_mask, kindSupport10_019_mask, kindSupport10_020_mask, kindSupport10_021_mask, kindSupport10_022_mask, kindSupport10_023_mask, kindSupport10_024_mask, kindSupport10_025_mask, kindSupport10_026_mask, kindSupport10_027_mask, kindSupport10_028_mask, kindSupport10_029_mask, kindSupport10_030_mask, kindSupport10_031_mask, kindSupport10_032_mask, kindSupport10_033_mask, kindSupport10_034_mask, kindSupport10_035_mask]
    decide +kernel
  · rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, kindSupport10_suffix_025, kindSupport10_suffix_026, kindSupport10_suffix_027, kindSupport10_suffix_028, kindSupport10_suffix_029, kindSupport10_suffix_030, kindSupport10_suffix_031, kindSupport10_suffix_032, kindSupport10_suffix_033, kindSupport10_suffix_034, kindSupport10_suffix_035, kindSupport10_suffix_036, List.all_append, List.all_nil, kindSupport10_000_checked, kindSupport10_001_checked, kindSupport10_002_checked, kindSupport10_003_checked, kindSupport10_004_checked, kindSupport10_005_checked, kindSupport10_006_checked, kindSupport10_007_checked, kindSupport10_008_checked, kindSupport10_009_checked, kindSupport10_010_checked, kindSupport10_011_checked, kindSupport10_012_checked, kindSupport10_013_checked, kindSupport10_014_checked, kindSupport10_015_checked, kindSupport10_016_checked, kindSupport10_017_checked, kindSupport10_018_checked, kindSupport10_019_checked, kindSupport10_020_checked, kindSupport10_021_checked, kindSupport10_022_checked, kindSupport10_023_checked, kindSupport10_024_checked, kindSupport10_025_checked, kindSupport10_026_checked, kindSupport10_027_checked, kindSupport10_028_checked, kindSupport10_029_checked, kindSupport10_030_checked, kindSupport10_031_checked, kindSupport10_032_checked, kindSupport10_033_checked, kindSupport10_034_checked, kindSupport10_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra04
