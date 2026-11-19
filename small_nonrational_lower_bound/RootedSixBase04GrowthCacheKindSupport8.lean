module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase04GrowthCacheKindSupport8Part000
public import RootedSixBase04GrowthCacheKindSupport8Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_5 8 011 12
cert_kindSupport_suffix_decode_4 8 010 12 16 16 011 011 0
cert_kindSupport_suffix_decode_4 8 009 12 48 32 011 010 16
cert_kindSupport_suffix_decode_4 8 008 12 80 32 011 009 48
cert_kindSupport_suffix_decode_4 8 007 12 112 32 011 008 80
cert_kindSupport_suffix_decode_4 8 006 12 144 32 011 007 112
cert_kindSupport_suffix_decode_4 8 005 12 176 32 011 006 144
cert_kindSupport_suffix_decode_4 8 004 12 208 32 011 005 176
cert_kindSupport_suffix_decode_4 8 003 12 240 32 011 004 208
cert_kindSupport_suffix_decode_4 8 002 12 272 32 011 003 240
cert_kindSupport_suffix_decode_4 8 001 12 304 32 011 002 272
cert_kindSupport_suffix_decode_4 8 000 12 336 32 011 001 304
theorem kindSupport8_eq : kindRows 8 = kindSupport8_suffix_000 := by
  change kindSupports 8 = kindSupport8_suffix_000
  rw [kindSupport8_source]
  exact congrArg Prod.fst kindSupport8_suffix_decode_000
theorem kindTest_large_8 : kindTest 8 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport8_eq]
    simp only [kindSupport8_suffix_000, kindSupport8_suffix_001, kindSupport8_suffix_002, kindSupport8_suffix_003, kindSupport8_suffix_004, kindSupport8_suffix_005, kindSupport8_suffix_006, kindSupport8_suffix_007, kindSupport8_suffix_008, kindSupport8_suffix_009, kindSupport8_suffix_010, kindSupport8_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport8_000_mask, kindSupport8_001_mask, kindSupport8_002_mask, kindSupport8_003_mask, kindSupport8_004_mask, kindSupport8_005_mask, kindSupport8_006_mask, kindSupport8_007_mask, kindSupport8_008_mask, kindSupport8_009_mask, kindSupport8_010_mask]
    decide +kernel
  · rw [kindSupport8_eq]
    simp only [kindSupport8_suffix_000, kindSupport8_suffix_001, kindSupport8_suffix_002, kindSupport8_suffix_003, kindSupport8_suffix_004, kindSupport8_suffix_005, kindSupport8_suffix_006, kindSupport8_suffix_007, kindSupport8_suffix_008, kindSupport8_suffix_009, kindSupport8_suffix_010, kindSupport8_suffix_011, List.all_append, List.all_nil, kindSupport8_000_checked, kindSupport8_001_checked, kindSupport8_002_checked, kindSupport8_003_checked, kindSupport8_004_checked, kindSupport8_005_checked, kindSupport8_006_checked, kindSupport8_007_checked, kindSupport8_008_checked, kindSupport8_009_checked, kindSupport8_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase04
