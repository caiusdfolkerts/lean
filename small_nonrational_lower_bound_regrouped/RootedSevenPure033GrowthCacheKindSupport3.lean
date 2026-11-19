module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public import RootedSevenPure033GrowthCacheKindSupport3Part000
public import RootedSevenPure033GrowthCacheKindSupport3Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure033
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_3 3 012 10
cert_kindSupport_suffix_decode_2 3 011 10 8 8 012 012 0
cert_kindSupport_suffix_decode_2 3 010 10 40 32 012 011 8
cert_kindSupport_suffix_decode_2 3 009 10 72 32 012 010 40
cert_kindSupport_suffix_decode_2 3 008 10 104 32 012 009 72
cert_kindSupport_suffix_decode_2 3 007 10 136 32 012 008 104
cert_kindSupport_suffix_decode_2 3 006 10 168 32 012 007 136
cert_kindSupport_suffix_decode_2 3 005 10 200 32 012 006 168
cert_kindSupport_suffix_decode_2 3 004 10 232 32 012 005 200
cert_kindSupport_suffix_decode_2 3 003 10 264 32 012 004 232
cert_kindSupport_suffix_decode_2 3 002 10 296 32 012 003 264
cert_kindSupport_suffix_decode_2 3 001 10 328 32 012 002 296
cert_kindSupport_suffix_decode_2 3 000 10 360 32 012 001 328
cert_kindSupport_eq 3
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask, kindSupport3_009_mask, kindSupport3_010_mask, kindSupport3_011_mask]
    decide +kernel
  · rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, kindSupport3_009_checked, kindSupport3_010_checked, kindSupport3_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenPure033
