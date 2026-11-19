module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05GrowthCacheKindSupport10Part000
public import RootedSixExtra05GrowthCacheKindSupport10Part001
public import RootedSixExtra05GrowthCacheKindSupport10Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 10 018 12
cert_kindSupport_suffix_decode_6 10 017 12 32 32 018 018 0
cert_kindSupport_suffix_decode_6 10 016 12 64 32 018 017 32
cert_kindSupport_suffix_decode_6 10 015 12 96 32 018 016 64
cert_kindSupport_suffix_decode_6 10 014 12 128 32 018 015 96
cert_kindSupport_suffix_decode_6 10 013 12 160 32 018 014 128
cert_kindSupport_suffix_decode_6 10 012 12 192 32 018 013 160
cert_kindSupport_suffix_decode_6 10 011 12 224 32 018 012 192
cert_kindSupport_suffix_decode_6 10 010 12 256 32 018 011 224
cert_kindSupport_suffix_decode_6 10 009 12 288 32 018 010 256
cert_kindSupport_suffix_decode_6 10 008 12 320 32 018 009 288
cert_kindSupport_suffix_decode_6 10 007 12 352 32 018 008 320
cert_kindSupport_suffix_decode_6 10 006 12 384 32 018 007 352
cert_kindSupport_suffix_decode_6 10 005 12 416 32 018 006 384
cert_kindSupport_suffix_decode_6 10 004 12 448 32 018 005 416
cert_kindSupport_suffix_decode_6 10 003 12 480 32 018 004 448
cert_kindSupport_suffix_decode_6 10 002 12 512 32 018 003 480
cert_kindSupport_suffix_decode_6 10 001 12 544 32 018 002 512
cert_kindSupport_suffix_decode_6 10 000 12 576 32 018 001 544
cert_kindSupport_eq_3 10
theorem kindTest_large_10 : kindTest 10 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport10_000_mask, kindSupport10_001_mask, kindSupport10_002_mask, kindSupport10_003_mask, kindSupport10_004_mask, kindSupport10_005_mask, kindSupport10_006_mask, kindSupport10_007_mask, kindSupport10_008_mask, kindSupport10_009_mask, kindSupport10_010_mask, kindSupport10_011_mask, kindSupport10_012_mask, kindSupport10_013_mask, kindSupport10_014_mask, kindSupport10_015_mask, kindSupport10_016_mask, kindSupport10_017_mask]
    decide +kernel
  · rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, List.all_append, List.all_nil, kindSupport10_000_checked, kindSupport10_001_checked, kindSupport10_002_checked, kindSupport10_003_checked, kindSupport10_004_checked, kindSupport10_005_checked, kindSupport10_006_checked, kindSupport10_007_checked, kindSupport10_008_checked, kindSupport10_009_checked, kindSupport10_010_checked, kindSupport10_011_checked, kindSupport10_012_checked, kindSupport10_013_checked, kindSupport10_014_checked, kindSupport10_015_checked, kindSupport10_016_checked, kindSupport10_017_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
