module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra01GrowthCacheKindSupport10Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 10 030 12
cert_kindSupport_suffix_decode_6 10 029 12 32 32 030 030 0
cert_kindSupport_suffix_decode_6 10 028 12 64 32 030 029 32
cert_kindSupport_suffix_decode_6 10 027 12 96 32 030 028 64
cert_kindSupport_suffix_decode_6 10 026 12 128 32 030 027 96
cert_kindSupport_suffix_decode_6 10 025 12 160 32 030 026 128
cert_kindSupport_suffix_decode_6 10 024 12 192 32 030 025 160
cert_kindSupport_suffix_decode_6 10 023 12 224 32 030 024 192
cert_kindSupport_suffix_decode_6 10 022 12 256 32 030 023 224
cert_kindSupport_suffix_decode_6 10 021 12 288 32 030 022 256
cert_kindSupport_suffix_decode_6 10 020 12 320 32 030 021 288
cert_kindSupport_suffix_decode_6 10 019 12 352 32 030 020 320
cert_kindSupport_suffix_decode_6 10 018 12 384 32 030 019 352
cert_kindSupport_suffix_decode_6 10 017 12 416 32 030 018 384
cert_kindSupport_suffix_decode_6 10 016 12 448 32 030 017 416
cert_kindSupport_suffix_decode_6 10 015 12 480 32 030 016 448
cert_kindSupport_suffix_decode_6 10 014 12 512 32 030 015 480
cert_kindSupport_suffix_decode_6 10 013 12 544 32 030 014 512
cert_kindSupport_suffix_decode_6 10 012 12 576 32 030 013 544
cert_kindSupport_suffix_decode_6 10 011 12 608 32 030 012 576
cert_kindSupport_suffix_decode_6 10 010 12 640 32 030 011 608
cert_kindSupport_suffix_decode_6 10 009 12 672 32 030 010 640
cert_kindSupport_suffix_decode_6 10 008 12 704 32 030 009 672
cert_kindSupport_suffix_decode_6 10 007 12 736 32 030 008 704
cert_kindSupport_suffix_decode_6 10 006 12 768 32 030 007 736
cert_kindSupport_suffix_decode_6 10 005 12 800 32 030 006 768
cert_kindSupport_suffix_decode_6 10 004 12 832 32 030 005 800
cert_kindSupport_suffix_decode_6 10 003 12 864 32 030 004 832
cert_kindSupport_suffix_decode_6 10 002 12 896 32 030 003 864
cert_kindSupport_suffix_decode_6 10 001 12 928 32 030 002 896
cert_kindSupport_suffix_decode_6 10 000 12 960 32 030 001 928
cert_kindSupport_eq_3 10
theorem kindTest_large_10 : kindTest 10 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, kindSupport10_suffix_025, kindSupport10_suffix_026, kindSupport10_suffix_027, kindSupport10_suffix_028, kindSupport10_suffix_029, kindSupport10_suffix_030, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport10_000_mask, kindSupport10_001_mask, kindSupport10_002_mask, kindSupport10_003_mask, kindSupport10_004_mask, kindSupport10_005_mask, kindSupport10_006_mask, kindSupport10_007_mask, kindSupport10_008_mask, kindSupport10_009_mask, kindSupport10_010_mask, kindSupport10_011_mask, kindSupport10_012_mask, kindSupport10_013_mask, kindSupport10_014_mask, kindSupport10_015_mask, kindSupport10_016_mask, kindSupport10_017_mask, kindSupport10_018_mask, kindSupport10_019_mask, kindSupport10_020_mask, kindSupport10_021_mask, kindSupport10_022_mask, kindSupport10_023_mask, kindSupport10_024_mask, kindSupport10_025_mask, kindSupport10_026_mask, kindSupport10_027_mask, kindSupport10_028_mask, kindSupport10_029_mask]
    decide +kernel
  · rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, kindSupport10_suffix_025, kindSupport10_suffix_026, kindSupport10_suffix_027, kindSupport10_suffix_028, kindSupport10_suffix_029, kindSupport10_suffix_030, List.all_append, List.all_nil, kindSupport10_000_checked, kindSupport10_001_checked, kindSupport10_002_checked, kindSupport10_003_checked, kindSupport10_004_checked, kindSupport10_005_checked, kindSupport10_006_checked, kindSupport10_007_checked, kindSupport10_008_checked, kindSupport10_009_checked, kindSupport10_010_checked, kindSupport10_011_checked, kindSupport10_012_checked, kindSupport10_013_checked, kindSupport10_014_checked, kindSupport10_015_checked, kindSupport10_016_checked, kindSupport10_017_checked, kindSupport10_018_checked, kindSupport10_019_checked, kindSupport10_020_checked, kindSupport10_021_checked, kindSupport10_022_checked, kindSupport10_023_checked, kindSupport10_024_checked, kindSupport10_025_checked, kindSupport10_026_checked, kindSupport10_027_checked, kindSupport10_028_checked, kindSupport10_029_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra01
