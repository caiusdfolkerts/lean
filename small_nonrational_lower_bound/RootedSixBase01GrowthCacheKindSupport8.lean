module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase01GrowthCacheKindSupport8Part000
public import RootedSixBase01GrowthCacheKindSupport8Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_5 8 009 14
cert_kindSupport_suffix_decode_4 8 008 14 20 20 009 009 0
cert_kindSupport_suffix_decode_4 8 007 14 52 32 009 008 20
cert_kindSupport_suffix_decode_4 8 006 14 84 32 009 007 52
cert_kindSupport_suffix_decode_4 8 005 14 116 32 009 006 84
cert_kindSupport_suffix_decode_4 8 004 14 148 32 009 005 116
cert_kindSupport_suffix_decode_4 8 003 14 180 32 009 004 148
cert_kindSupport_suffix_decode_4 8 002 14 212 32 009 003 180
cert_kindSupport_suffix_decode_4 8 001 14 244 32 009 002 212
cert_kindSupport_suffix_decode_4 8 000 14 276 32 009 001 244
cert_kindSupport_eq_2 8
theorem kindTest_large_8 : kindTest 8 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport8_eq]
    simp only [kindSupport8_suffix_000, kindSupport8_suffix_001, kindSupport8_suffix_002, kindSupport8_suffix_003, kindSupport8_suffix_004, kindSupport8_suffix_005, kindSupport8_suffix_006, kindSupport8_suffix_007, kindSupport8_suffix_008, kindSupport8_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport8_000_mask, kindSupport8_001_mask, kindSupport8_002_mask, kindSupport8_003_mask, kindSupport8_004_mask, kindSupport8_005_mask, kindSupport8_006_mask, kindSupport8_007_mask, kindSupport8_008_mask]
    decide +kernel
  · rw [kindSupport8_eq]
    simp only [kindSupport8_suffix_000, kindSupport8_suffix_001, kindSupport8_suffix_002, kindSupport8_suffix_003, kindSupport8_suffix_004, kindSupport8_suffix_005, kindSupport8_suffix_006, kindSupport8_suffix_007, kindSupport8_suffix_008, kindSupport8_suffix_009, List.all_append, List.all_nil, kindSupport8_000_checked, kindSupport8_001_checked, kindSupport8_002_checked, kindSupport8_003_checked, kindSupport8_004_checked, kindSupport8_005_checked, kindSupport8_006_checked, kindSupport8_007_checked, kindSupport8_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
