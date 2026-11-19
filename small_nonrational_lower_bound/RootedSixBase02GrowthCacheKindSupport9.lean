module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase02GrowthCacheKindSupport9Part000
public import RootedSixBase02GrowthCacheKindSupport9Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_5 9 016 13
cert_kindSupport_suffix_decode_4 9 015 13 24 24 016 016 0
cert_kindSupport_suffix_decode_4 9 014 13 56 32 016 015 24
cert_kindSupport_suffix_decode_4 9 013 13 88 32 016 014 56
cert_kindSupport_suffix_decode_4 9 012 13 120 32 016 013 88
cert_kindSupport_suffix_decode_4 9 011 13 152 32 016 012 120
cert_kindSupport_suffix_decode_4 9 010 13 184 32 016 011 152
cert_kindSupport_suffix_decode_4 9 009 13 216 32 016 010 184
cert_kindSupport_suffix_decode_4 9 008 13 248 32 016 009 216
cert_kindSupport_suffix_decode_4 9 007 13 280 32 016 008 248
cert_kindSupport_suffix_decode_4 9 006 13 312 32 016 007 280
cert_kindSupport_suffix_decode_4 9 005 13 344 32 016 006 312
cert_kindSupport_suffix_decode_4 9 004 13 376 32 016 005 344
cert_kindSupport_suffix_decode_4 9 003 13 408 32 016 004 376
cert_kindSupport_suffix_decode_4 9 002 13 440 32 016 003 408
cert_kindSupport_suffix_decode_4 9 001 13 472 32 016 002 440
cert_kindSupport_suffix_decode_4 9 000 13 504 32 016 001 472
theorem kindSupport9_eq : kindRows 9 = kindSupport9_suffix_000 := by
  change kindSupports 9 = kindSupport9_suffix_000
  rw [kindSupport9_source]
  exact congrArg Prod.fst kindSupport9_suffix_decode_000
theorem kindTest_large_9 : kindTest 9 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, kindSupport9_suffix_015, kindSupport9_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport9_000_mask, kindSupport9_001_mask, kindSupport9_002_mask, kindSupport9_003_mask, kindSupport9_004_mask, kindSupport9_005_mask, kindSupport9_006_mask, kindSupport9_007_mask, kindSupport9_008_mask, kindSupport9_009_mask, kindSupport9_010_mask, kindSupport9_011_mask, kindSupport9_012_mask, kindSupport9_013_mask, kindSupport9_014_mask, kindSupport9_015_mask]
    decide +kernel
  · rw [kindSupport9_eq]
    simp only [kindSupport9_suffix_000, kindSupport9_suffix_001, kindSupport9_suffix_002, kindSupport9_suffix_003, kindSupport9_suffix_004, kindSupport9_suffix_005, kindSupport9_suffix_006, kindSupport9_suffix_007, kindSupport9_suffix_008, kindSupport9_suffix_009, kindSupport9_suffix_010, kindSupport9_suffix_011, kindSupport9_suffix_012, kindSupport9_suffix_013, kindSupport9_suffix_014, kindSupport9_suffix_015, kindSupport9_suffix_016, List.all_append, List.all_nil, kindSupport9_000_checked, kindSupport9_001_checked, kindSupport9_002_checked, kindSupport9_003_checked, kindSupport9_004_checked, kindSupport9_005_checked, kindSupport9_006_checked, kindSupport9_007_checked, kindSupport9_008_checked, kindSupport9_009_checked, kindSupport9_010_checked, kindSupport9_011_checked, kindSupport9_012_checked, kindSupport9_013_checked, kindSupport9_014_checked, kindSupport9_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
