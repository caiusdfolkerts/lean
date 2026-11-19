module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase01GrowthCacheKindSupport2Part000
public import RootedSixBase01GrowthCacheKindSupport2Part001
public import RootedSixBase01GrowthCacheKindSupport2Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_5 2 021 14
cert_kindSupport_suffix_decode_4 2 020 14 32 32 021 021 0
cert_kindSupport_suffix_decode_4 2 019 14 64 32 021 020 32
cert_kindSupport_suffix_decode_4 2 018 14 96 32 021 019 64
cert_kindSupport_suffix_decode_4 2 017 14 128 32 021 018 96
cert_kindSupport_suffix_decode_4 2 016 14 160 32 021 017 128
cert_kindSupport_suffix_decode_4 2 015 14 192 32 021 016 160
cert_kindSupport_suffix_decode_4 2 014 14 224 32 021 015 192
cert_kindSupport_suffix_decode_4 2 013 14 256 32 021 014 224
cert_kindSupport_suffix_decode_4 2 012 14 288 32 021 013 256
cert_kindSupport_suffix_decode_4 2 011 14 320 32 021 012 288
cert_kindSupport_suffix_decode_4 2 010 14 352 32 021 011 320
cert_kindSupport_suffix_decode_4 2 009 14 384 32 021 010 352
cert_kindSupport_suffix_decode_4 2 008 14 416 32 021 009 384
cert_kindSupport_suffix_decode_4 2 007 14 448 32 021 008 416
cert_kindSupport_suffix_decode_4 2 006 14 480 32 021 007 448
cert_kindSupport_suffix_decode_4 2 005 14 512 32 021 006 480
cert_kindSupport_suffix_decode_4 2 004 14 544 32 021 005 512
cert_kindSupport_suffix_decode_4 2 003 14 576 32 021 004 544
cert_kindSupport_suffix_decode_4 2 002 14 608 32 021 003 576
cert_kindSupport_suffix_decode_4 2 001 14 640 32 021 002 608
cert_kindSupport_suffix_decode_4 2 000 14 672 32 021 001 640
cert_kindSupport_eq_2 2
theorem kindTest_large_2 : kindTest 2 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, kindSupport2_suffix_019, kindSupport2_suffix_020, kindSupport2_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport2_000_mask, kindSupport2_001_mask, kindSupport2_002_mask, kindSupport2_003_mask, kindSupport2_004_mask, kindSupport2_005_mask, kindSupport2_006_mask, kindSupport2_007_mask, kindSupport2_008_mask, kindSupport2_009_mask, kindSupport2_010_mask, kindSupport2_011_mask, kindSupport2_012_mask, kindSupport2_013_mask, kindSupport2_014_mask, kindSupport2_015_mask, kindSupport2_016_mask, kindSupport2_017_mask, kindSupport2_018_mask, kindSupport2_019_mask, kindSupport2_020_mask]
    decide +kernel
  · rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, kindSupport2_suffix_019, kindSupport2_suffix_020, kindSupport2_suffix_021, List.all_append, List.all_nil, kindSupport2_000_checked, kindSupport2_001_checked, kindSupport2_002_checked, kindSupport2_003_checked, kindSupport2_004_checked, kindSupport2_005_checked, kindSupport2_006_checked, kindSupport2_007_checked, kindSupport2_008_checked, kindSupport2_009_checked, kindSupport2_010_checked, kindSupport2_011_checked, kindSupport2_012_checked, kindSupport2_013_checked, kindSupport2_014_checked, kindSupport2_015_checked, kindSupport2_016_checked, kindSupport2_017_checked, kindSupport2_018_checked, kindSupport2_019_checked, kindSupport2_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
