module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra06GrowthCacheKindSupport2Part000
public import RootedSixExtra06GrowthCacheKindSupport2Part001
public import RootedSixExtra06GrowthCacheKindSupport2Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 2 019 12
cert_kindSupport_suffix_decode_6 2 018 12 24 24 019 019 0
cert_kindSupport_suffix_decode_6 2 017 12 56 32 019 018 24
cert_kindSupport_suffix_decode_6 2 016 12 88 32 019 017 56
cert_kindSupport_suffix_decode_6 2 015 12 120 32 019 016 88
cert_kindSupport_suffix_decode_6 2 014 12 152 32 019 015 120
cert_kindSupport_suffix_decode_6 2 013 12 184 32 019 014 152
cert_kindSupport_suffix_decode_6 2 012 12 216 32 019 013 184
cert_kindSupport_suffix_decode_6 2 011 12 248 32 019 012 216
cert_kindSupport_suffix_decode_6 2 010 12 280 32 019 011 248
cert_kindSupport_suffix_decode_6 2 009 12 312 32 019 010 280
cert_kindSupport_suffix_decode_6 2 008 12 344 32 019 009 312
cert_kindSupport_suffix_decode_6 2 007 12 376 32 019 008 344
cert_kindSupport_suffix_decode_6 2 006 12 408 32 019 007 376
cert_kindSupport_suffix_decode_6 2 005 12 440 32 019 006 408
cert_kindSupport_suffix_decode_6 2 004 12 472 32 019 005 440
cert_kindSupport_suffix_decode_6 2 003 12 504 32 019 004 472
cert_kindSupport_suffix_decode_6 2 002 12 536 32 019 003 504
cert_kindSupport_suffix_decode_6 2 001 12 568 32 019 002 536
cert_kindSupport_suffix_decode_6 2 000 12 600 32 019 001 568
cert_kindSupport_eq_3 2
theorem kindTest_large_2 : kindTest 2 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, kindSupport2_suffix_019, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport2_000_mask, kindSupport2_001_mask, kindSupport2_002_mask, kindSupport2_003_mask, kindSupport2_004_mask, kindSupport2_005_mask, kindSupport2_006_mask, kindSupport2_007_mask, kindSupport2_008_mask, kindSupport2_009_mask, kindSupport2_010_mask, kindSupport2_011_mask, kindSupport2_012_mask, kindSupport2_013_mask, kindSupport2_014_mask, kindSupport2_015_mask, kindSupport2_016_mask, kindSupport2_017_mask, kindSupport2_018_mask]
    decide +kernel
  · rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, kindSupport2_suffix_019, List.all_append, List.all_nil, kindSupport2_000_checked, kindSupport2_001_checked, kindSupport2_002_checked, kindSupport2_003_checked, kindSupport2_004_checked, kindSupport2_005_checked, kindSupport2_006_checked, kindSupport2_007_checked, kindSupport2_008_checked, kindSupport2_009_checked, kindSupport2_010_checked, kindSupport2_011_checked, kindSupport2_012_checked, kindSupport2_013_checked, kindSupport2_014_checked, kindSupport2_015_checked, kindSupport2_016_checked, kindSupport2_017_checked, kindSupport2_018_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
