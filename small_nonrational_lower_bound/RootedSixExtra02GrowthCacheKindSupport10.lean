module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra02GrowthCacheKindSupport10Part000
public import RootedSixExtra02GrowthCacheKindSupport10Part001
public import RootedSixExtra02GrowthCacheKindSupport10Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 10 024 13
cert_kindSupport_suffix_decode_6 10 023 13 32 32 024 024 0
cert_kindSupport_suffix_decode_6 10 022 13 64 32 024 023 32
cert_kindSupport_suffix_decode_6 10 021 13 96 32 024 022 64
cert_kindSupport_suffix_decode_6 10 020 13 128 32 024 021 96
cert_kindSupport_suffix_decode_6 10 019 13 160 32 024 020 128
cert_kindSupport_suffix_decode_6 10 018 13 192 32 024 019 160
cert_kindSupport_suffix_decode_6 10 017 13 224 32 024 018 192
cert_kindSupport_suffix_decode_6 10 016 13 256 32 024 017 224
cert_kindSupport_suffix_decode_6 10 015 13 288 32 024 016 256
cert_kindSupport_suffix_decode_6 10 014 13 320 32 024 015 288
cert_kindSupport_suffix_decode_6 10 013 13 352 32 024 014 320
cert_kindSupport_suffix_decode_6 10 012 13 384 32 024 013 352
cert_kindSupport_suffix_decode_6 10 011 13 416 32 024 012 384
cert_kindSupport_suffix_decode_6 10 010 13 448 32 024 011 416
cert_kindSupport_suffix_decode_6 10 009 13 480 32 024 010 448
cert_kindSupport_suffix_decode_6 10 008 13 512 32 024 009 480
cert_kindSupport_suffix_decode_6 10 007 13 544 32 024 008 512
cert_kindSupport_suffix_decode_6 10 006 13 576 32 024 007 544
cert_kindSupport_suffix_decode_6 10 005 13 608 32 024 006 576
cert_kindSupport_suffix_decode_6 10 004 13 640 32 024 005 608
cert_kindSupport_suffix_decode_6 10 003 13 672 32 024 004 640
cert_kindSupport_suffix_decode_6 10 002 13 704 32 024 003 672
cert_kindSupport_suffix_decode_6 10 001 13 736 32 024 002 704
cert_kindSupport_suffix_decode_6 10 000 13 768 32 024 001 736
cert_kindSupport_eq_3 10
theorem kindTest_large_10 : kindTest 10 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport10_000_mask, kindSupport10_001_mask, kindSupport10_002_mask, kindSupport10_003_mask, kindSupport10_004_mask, kindSupport10_005_mask, kindSupport10_006_mask, kindSupport10_007_mask, kindSupport10_008_mask, kindSupport10_009_mask, kindSupport10_010_mask, kindSupport10_011_mask, kindSupport10_012_mask, kindSupport10_013_mask, kindSupport10_014_mask, kindSupport10_015_mask, kindSupport10_016_mask, kindSupport10_017_mask, kindSupport10_018_mask, kindSupport10_019_mask, kindSupport10_020_mask, kindSupport10_021_mask, kindSupport10_022_mask, kindSupport10_023_mask]
    decide +kernel
  · rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, List.all_append, List.all_nil, kindSupport10_000_checked, kindSupport10_001_checked, kindSupport10_002_checked, kindSupport10_003_checked, kindSupport10_004_checked, kindSupport10_005_checked, kindSupport10_006_checked, kindSupport10_007_checked, kindSupport10_008_checked, kindSupport10_009_checked, kindSupport10_010_checked, kindSupport10_011_checked, kindSupport10_012_checked, kindSupport10_013_checked, kindSupport10_014_checked, kindSupport10_015_checked, kindSupport10_016_checked, kindSupport10_017_checked, kindSupport10_018_checked, kindSupport10_019_checked, kindSupport10_020_checked, kindSupport10_021_checked, kindSupport10_022_checked, kindSupport10_023_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
