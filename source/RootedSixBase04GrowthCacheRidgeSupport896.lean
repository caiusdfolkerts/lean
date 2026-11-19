module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase04GrowthCacheRidgeSupport896PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 896 015 12
cert_ridgeSupport_suffix_decode_2 896 014 12 15 15 015 015 0
cert_ridgeSupport_suffix_decode_2 896 013 12 47 32 015 014 15
cert_ridgeSupport_suffix_decode_2 896 012 12 79 32 015 013 47
cert_ridgeSupport_suffix_decode_2 896 011 12 111 32 015 012 79
cert_ridgeSupport_suffix_decode_2 896 010 12 143 32 015 011 111
cert_ridgeSupport_suffix_decode_2 896 009 12 175 32 015 010 143
cert_ridgeSupport_suffix_decode_2 896 008 12 207 32 015 009 175
cert_ridgeSupport_suffix_decode_2 896 007 12 239 32 015 008 207
cert_ridgeSupport_suffix_decode_2 896 006 12 271 32 015 007 239
cert_ridgeSupport_suffix_decode_2 896 005 12 303 32 015 006 271
cert_ridgeSupport_suffix_decode_2 896 004 12 335 32 015 005 303
cert_ridgeSupport_suffix_decode_2 896 003 12 367 32 015 004 335
cert_ridgeSupport_suffix_decode_2 896 002 12 399 32 015 003 367
cert_ridgeSupport_suffix_decode_2 896 001 12 431 32 015 002 399
cert_ridgeSupport_suffix_decode_2 896 000 12 463 32 015 001 431
cert_ridgeSupport_eq 896
theorem ridgeTest_large_896 : ridgeTest 896 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport896_000_mask, ridgeSupport896_001_mask, ridgeSupport896_002_mask, ridgeSupport896_003_mask, ridgeSupport896_004_mask, ridgeSupport896_005_mask, ridgeSupport896_006_mask, ridgeSupport896_007_mask, ridgeSupport896_008_mask, ridgeSupport896_009_mask, ridgeSupport896_010_mask, ridgeSupport896_011_mask, ridgeSupport896_012_mask, ridgeSupport896_013_mask, ridgeSupport896_014_mask]
    decide +kernel
  · rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, List.all_append, List.all_nil, ridgeSupport896_000_checked, ridgeSupport896_001_checked, ridgeSupport896_002_checked, ridgeSupport896_003_checked, ridgeSupport896_004_checked, ridgeSupport896_005_checked, ridgeSupport896_006_checked, ridgeSupport896_007_checked, ridgeSupport896_008_checked, ridgeSupport896_009_checked, ridgeSupport896_010_checked, ridgeSupport896_011_checked, ridgeSupport896_012_checked, ridgeSupport896_013_checked, ridgeSupport896_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase04
