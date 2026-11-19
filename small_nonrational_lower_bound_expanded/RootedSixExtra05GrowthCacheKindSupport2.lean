module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05GrowthCacheKindSupport2Part000
public import RootedSixExtra05GrowthCacheKindSupport2Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 2 015 12
cert_kindSupport_suffix_decode_6 2 014 12 8 8 015 015 0
cert_kindSupport_suffix_decode_6 2 013 12 40 32 015 014 8
cert_kindSupport_suffix_decode_6 2 012 12 72 32 015 013 40
cert_kindSupport_suffix_decode_6 2 011 12 104 32 015 012 72
cert_kindSupport_suffix_decode_6 2 010 12 136 32 015 011 104
cert_kindSupport_suffix_decode_6 2 009 12 168 32 015 010 136
cert_kindSupport_suffix_decode_6 2 008 12 200 32 015 009 168
cert_kindSupport_suffix_decode_6 2 007 12 232 32 015 008 200
cert_kindSupport_suffix_decode_6 2 006 12 264 32 015 007 232
cert_kindSupport_suffix_decode_6 2 005 12 296 32 015 006 264
cert_kindSupport_suffix_decode_6 2 004 12 328 32 015 005 296
cert_kindSupport_suffix_decode_6 2 003 12 360 32 015 004 328
cert_kindSupport_suffix_decode_6 2 002 12 392 32 015 003 360
cert_kindSupport_suffix_decode_6 2 001 12 424 32 015 002 392
cert_kindSupport_suffix_decode_6 2 000 12 456 32 015 001 424
cert_kindSupport_eq_3 2
theorem kindTest_large_2 : kindTest 2 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport2_000_mask, kindSupport2_001_mask, kindSupport2_002_mask, kindSupport2_003_mask, kindSupport2_004_mask, kindSupport2_005_mask, kindSupport2_006_mask, kindSupport2_007_mask, kindSupport2_008_mask, kindSupport2_009_mask, kindSupport2_010_mask, kindSupport2_011_mask, kindSupport2_012_mask, kindSupport2_013_mask, kindSupport2_014_mask]
    decide +kernel
  · rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, List.all_append, List.all_nil, kindSupport2_000_checked, kindSupport2_001_checked, kindSupport2_002_checked, kindSupport2_003_checked, kindSupport2_004_checked, kindSupport2_005_checked, kindSupport2_006_checked, kindSupport2_007_checked, kindSupport2_008_checked, kindSupport2_009_checked, kindSupport2_010_checked, kindSupport2_011_checked, kindSupport2_012_checked, kindSupport2_013_checked, kindSupport2_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
