module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05GrowthCacheKindSupport3Part000
public import RootedSixExtra05GrowthCacheKindSupport3Part001
public import RootedSixExtra05GrowthCacheKindSupport3Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 3 019 12
cert_kindSupport_suffix_decode_6 3 018 12 30 30 019 019 0
cert_kindSupport_suffix_decode_6 3 017 12 62 32 019 018 30
cert_kindSupport_suffix_decode_6 3 016 12 94 32 019 017 62
cert_kindSupport_suffix_decode_6 3 015 12 126 32 019 016 94
cert_kindSupport_suffix_decode_6 3 014 12 158 32 019 015 126
cert_kindSupport_suffix_decode_6 3 013 12 190 32 019 014 158
cert_kindSupport_suffix_decode_6 3 012 12 222 32 019 013 190
cert_kindSupport_suffix_decode_6 3 011 12 254 32 019 012 222
cert_kindSupport_suffix_decode_6 3 010 12 286 32 019 011 254
cert_kindSupport_suffix_decode_6 3 009 12 318 32 019 010 286
cert_kindSupport_suffix_decode_6 3 008 12 350 32 019 009 318
cert_kindSupport_suffix_decode_6 3 007 12 382 32 019 008 350
cert_kindSupport_suffix_decode_6 3 006 12 414 32 019 007 382
cert_kindSupport_suffix_decode_6 3 005 12 446 32 019 006 414
cert_kindSupport_suffix_decode_6 3 004 12 478 32 019 005 446
cert_kindSupport_suffix_decode_6 3 003 12 510 32 019 004 478
cert_kindSupport_suffix_decode_6 3 002 12 542 32 019 003 510
cert_kindSupport_suffix_decode_6 3 001 12 574 32 019 002 542
cert_kindSupport_suffix_decode_6 3 000 12 606 32 019 001 574
cert_kindSupport_eq_3 3
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask, kindSupport3_009_mask, kindSupport3_010_mask, kindSupport3_011_mask, kindSupport3_012_mask, kindSupport3_013_mask, kindSupport3_014_mask, kindSupport3_015_mask, kindSupport3_016_mask, kindSupport3_017_mask, kindSupport3_018_mask]
    decide +kernel
  · rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, kindSupport3_009_checked, kindSupport3_010_checked, kindSupport3_011_checked, kindSupport3_012_checked, kindSupport3_013_checked, kindSupport3_014_checked, kindSupport3_015_checked, kindSupport3_016_checked, kindSupport3_017_checked, kindSupport3_018_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
