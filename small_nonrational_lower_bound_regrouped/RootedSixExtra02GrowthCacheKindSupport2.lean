module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra02GrowthCacheKindSupport2Part000
public import RootedSixExtra02GrowthCacheKindSupport2Part001
public import RootedSixExtra02GrowthCacheKindSupport2Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 2 018 13
cert_kindSupport_suffix_decode_6 2 017 13 20 20 018 018 0
cert_kindSupport_suffix_decode_6 2 016 13 52 32 018 017 20
cert_kindSupport_suffix_decode_6 2 015 13 84 32 018 016 52
cert_kindSupport_suffix_decode_6 2 014 13 116 32 018 015 84
cert_kindSupport_suffix_decode_6 2 013 13 148 32 018 014 116
cert_kindSupport_suffix_decode_6 2 012 13 180 32 018 013 148
cert_kindSupport_suffix_decode_6 2 011 13 212 32 018 012 180
cert_kindSupport_suffix_decode_6 2 010 13 244 32 018 011 212
cert_kindSupport_suffix_decode_6 2 009 13 276 32 018 010 244
cert_kindSupport_suffix_decode_6 2 008 13 308 32 018 009 276
cert_kindSupport_suffix_decode_6 2 007 13 340 32 018 008 308
cert_kindSupport_suffix_decode_6 2 006 13 372 32 018 007 340
cert_kindSupport_suffix_decode_6 2 005 13 404 32 018 006 372
cert_kindSupport_suffix_decode_6 2 004 13 436 32 018 005 404
cert_kindSupport_suffix_decode_6 2 003 13 468 32 018 004 436
cert_kindSupport_suffix_decode_6 2 002 13 500 32 018 003 468
cert_kindSupport_suffix_decode_6 2 001 13 532 32 018 002 500
cert_kindSupport_suffix_decode_6 2 000 13 564 32 018 001 532
cert_kindSupport_eq_3 2
theorem kindTest_large_2 : kindTest 2 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport2_000_mask, kindSupport2_001_mask, kindSupport2_002_mask, kindSupport2_003_mask, kindSupport2_004_mask, kindSupport2_005_mask, kindSupport2_006_mask, kindSupport2_007_mask, kindSupport2_008_mask, kindSupport2_009_mask, kindSupport2_010_mask, kindSupport2_011_mask, kindSupport2_012_mask, kindSupport2_013_mask, kindSupport2_014_mask, kindSupport2_015_mask, kindSupport2_016_mask, kindSupport2_017_mask]
    decide +kernel
  · rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, List.all_append, List.all_nil, kindSupport2_000_checked, kindSupport2_001_checked, kindSupport2_002_checked, kindSupport2_003_checked, kindSupport2_004_checked, kindSupport2_005_checked, kindSupport2_006_checked, kindSupport2_007_checked, kindSupport2_008_checked, kindSupport2_009_checked, kindSupport2_010_checked, kindSupport2_011_checked, kindSupport2_012_checked, kindSupport2_013_checked, kindSupport2_014_checked, kindSupport2_015_checked, kindSupport2_016_checked, kindSupport2_017_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
