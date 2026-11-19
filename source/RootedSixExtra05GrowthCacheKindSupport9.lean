module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05GrowthCacheKindSupport9Part000
public import RootedSixExtra05GrowthCacheKindSupport9Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 9 014 12
cert_kindSupport_suffix_decode_6 9 013 12 28 28 014 014 0
cert_kindSupport_suffix_decode_6 9 012 12 60 32 014 013 28
cert_kindSupport_suffix_decode_6 9 011 12 92 32 014 012 60
cert_kindSupport_suffix_decode_6 9 010 12 124 32 014 011 92
cert_kindSupport_suffix_decode_6 9 009 12 156 32 014 010 124
cert_kindSupport_suffix_decode_6 9 008 12 188 32 014 009 156
cert_kindSupport_suffix_decode_6 9 007 12 220 32 014 008 188
cert_kindSupport_suffix_decode_6 9 006 12 252 32 014 007 220
cert_kindSupport_suffix_decode_6 9 005 12 284 32 014 006 252
cert_kindSupport_suffix_decode_6 9 004 12 316 32 014 005 284
cert_kindSupport_suffix_decode_6 9 003 12 348 32 014 004 316
cert_kindSupport_suffix_decode_6 9 002 12 380 32 014 003 348
cert_kindSupport_suffix_decode_6 9 001 12 412 32 014 002 380
cert_kindSupport_suffix_decode_6 9 000 12 444 32 014 001 412
cert_kindSupport_eq_3 9
theorem kindTest_large_9 : kindTest 9 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport9_000_mask, kindSupport9_001_mask, kindSupport9_002_mask, kindSupport9_003_mask, kindSupport9_004_mask, kindSupport9_005_mask, kindSupport9_006_mask, kindSupport9_007_mask, kindSupport9_008_mask, kindSupport9_009_mask, kindSupport9_010_mask, kindSupport9_011_mask, kindSupport9_012_mask, kindSupport9_013_mask]
    decide +kernel
  · rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, List.all_append, List.all_nil, kindSupport9_000_checked, kindSupport9_001_checked, kindSupport9_002_checked, kindSupport9_003_checked, kindSupport9_004_checked, kindSupport9_005_checked, kindSupport9_006_checked, kindSupport9_007_checked, kindSupport9_008_checked, kindSupport9_009_checked, kindSupport9_010_checked, kindSupport9_011_checked, kindSupport9_012_checked, kindSupport9_013_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
