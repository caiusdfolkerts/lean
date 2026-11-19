module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheKindSupport9Part000
public import RootedSixExtra00GrowthCacheKindSupport9Part001
public import RootedSixExtra00GrowthCacheKindSupport9Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 9 020 14
cert_kindSupport_suffix_decode_6 9 019 14 16 16 020 020 0
cert_kindSupport_suffix_decode_6 9 018 14 48 32 020 019 16
cert_kindSupport_suffix_decode_6 9 017 14 80 32 020 018 48
cert_kindSupport_suffix_decode_6 9 016 14 112 32 020 017 80
cert_kindSupport_suffix_decode_6 9 015 14 144 32 020 016 112
cert_kindSupport_suffix_decode_6 9 014 14 176 32 020 015 144
cert_kindSupport_suffix_decode_6 9 013 14 208 32 020 014 176
cert_kindSupport_suffix_decode_6 9 012 14 240 32 020 013 208
cert_kindSupport_suffix_decode_6 9 011 14 272 32 020 012 240
cert_kindSupport_suffix_decode_6 9 010 14 304 32 020 011 272
cert_kindSupport_suffix_decode_6 9 009 14 336 32 020 010 304
cert_kindSupport_suffix_decode_6 9 008 14 368 32 020 009 336
cert_kindSupport_suffix_decode_6 9 007 14 400 32 020 008 368
cert_kindSupport_suffix_decode_6 9 006 14 432 32 020 007 400
cert_kindSupport_suffix_decode_6 9 005 14 464 32 020 006 432
cert_kindSupport_suffix_decode_6 9 004 14 496 32 020 005 464
cert_kindSupport_suffix_decode_6 9 003 14 528 32 020 004 496
cert_kindSupport_suffix_decode_6 9 002 14 560 32 020 003 528
cert_kindSupport_suffix_decode_6 9 001 14 592 32 020 002 560
cert_kindSupport_suffix_decode_6 9 000 14 624 32 020 001 592
cert_kindSupport_eq_3 9
theorem kindTest_large_9 : kindTest 9 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, kindSupport9_suffix_015, kindSupport9_suffix_016, kindSupport9_suffix_017, kindSupport9_suffix_018, kindSupport9_suffix_019, kindSupport9_suffix_020, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport9_000_mask, kindSupport9_001_mask, kindSupport9_002_mask, kindSupport9_003_mask, kindSupport9_004_mask, kindSupport9_005_mask, kindSupport9_006_mask, kindSupport9_007_mask, kindSupport9_008_mask, kindSupport9_009_mask, kindSupport9_010_mask, kindSupport9_011_mask, kindSupport9_012_mask, kindSupport9_013_mask, kindSupport9_014_mask, kindSupport9_015_mask, kindSupport9_016_mask, kindSupport9_017_mask, kindSupport9_018_mask, kindSupport9_019_mask]
    decide +kernel
  · rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, kindSupport9_suffix_015, kindSupport9_suffix_016, kindSupport9_suffix_017, kindSupport9_suffix_018, kindSupport9_suffix_019, kindSupport9_suffix_020, List.all_append, List.all_nil, kindSupport9_000_checked, kindSupport9_001_checked, kindSupport9_002_checked, kindSupport9_003_checked, kindSupport9_004_checked, kindSupport9_005_checked, kindSupport9_006_checked, kindSupport9_007_checked, kindSupport9_008_checked, kindSupport9_009_checked, kindSupport9_010_checked, kindSupport9_011_checked, kindSupport9_012_checked, kindSupport9_013_checked, kindSupport9_014_checked, kindSupport9_015_checked, kindSupport9_016_checked, kindSupport9_017_checked, kindSupport9_018_checked, kindSupport9_019_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
