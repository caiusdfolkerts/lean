module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase01GrowthCacheKindSupport9Part000
public import RootedSixBase01GrowthCacheKindSupport9Part001
public import RootedSixBase01GrowthCacheKindSupport9Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_5 9 018 14
cert_kindSupport_suffix_decode_4 9 017 14 20 20 018 018 0
cert_kindSupport_suffix_decode_4 9 016 14 52 32 018 017 20
cert_kindSupport_suffix_decode_4 9 015 14 84 32 018 016 52
cert_kindSupport_suffix_decode_4 9 014 14 116 32 018 015 84
cert_kindSupport_suffix_decode_4 9 013 14 148 32 018 014 116
cert_kindSupport_suffix_decode_4 9 012 14 180 32 018 013 148
cert_kindSupport_suffix_decode_4 9 011 14 212 32 018 012 180
cert_kindSupport_suffix_decode_4 9 010 14 244 32 018 011 212
cert_kindSupport_suffix_decode_4 9 009 14 276 32 018 010 244
cert_kindSupport_suffix_decode_4 9 008 14 308 32 018 009 276
cert_kindSupport_suffix_decode_4 9 007 14 340 32 018 008 308
cert_kindSupport_suffix_decode_4 9 006 14 372 32 018 007 340
cert_kindSupport_suffix_decode_4 9 005 14 404 32 018 006 372
cert_kindSupport_suffix_decode_4 9 004 14 436 32 018 005 404
cert_kindSupport_suffix_decode_4 9 003 14 468 32 018 004 436
cert_kindSupport_suffix_decode_4 9 002 14 500 32 018 003 468
cert_kindSupport_suffix_decode_4 9 001 14 532 32 018 002 500
cert_kindSupport_suffix_decode_4 9 000 14 564 32 018 001 532
cert_kindSupport_eq_2 9
theorem kindTest_large_9 : kindTest 9 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, kindSupport9_suffix_015, kindSupport9_suffix_016, kindSupport9_suffix_017, kindSupport9_suffix_018, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport9_000_mask, kindSupport9_001_mask, kindSupport9_002_mask, kindSupport9_003_mask, kindSupport9_004_mask, kindSupport9_005_mask, kindSupport9_006_mask, kindSupport9_007_mask, kindSupport9_008_mask, kindSupport9_009_mask, kindSupport9_010_mask, kindSupport9_011_mask, kindSupport9_012_mask, kindSupport9_013_mask, kindSupport9_014_mask, kindSupport9_015_mask, kindSupport9_016_mask, kindSupport9_017_mask]
    decide +kernel
  · rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, kindSupport9_suffix_015, kindSupport9_suffix_016, kindSupport9_suffix_017, kindSupport9_suffix_018, List.all_append, List.all_nil, kindSupport9_000_checked, kindSupport9_001_checked, kindSupport9_002_checked, kindSupport9_003_checked, kindSupport9_004_checked, kindSupport9_005_checked, kindSupport9_006_checked, kindSupport9_007_checked, kindSupport9_008_checked, kindSupport9_009_checked, kindSupport9_010_checked, kindSupport9_011_checked, kindSupport9_012_checked, kindSupport9_013_checked, kindSupport9_014_checked, kindSupport9_015_checked, kindSupport9_016_checked, kindSupport9_017_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
