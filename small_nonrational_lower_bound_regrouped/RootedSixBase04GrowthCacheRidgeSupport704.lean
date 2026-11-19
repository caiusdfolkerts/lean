module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase04GrowthCacheRidgeSupport704PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 704 015 12
cert_ridgeSupport_suffix_decode_2 704 014 12 15 15 015 015 0
cert_ridgeSupport_suffix_decode_2 704 013 12 47 32 015 014 15
cert_ridgeSupport_suffix_decode_2 704 012 12 79 32 015 013 47
cert_ridgeSupport_suffix_decode_2 704 011 12 111 32 015 012 79
cert_ridgeSupport_suffix_decode_2 704 010 12 143 32 015 011 111
cert_ridgeSupport_suffix_decode_2 704 009 12 175 32 015 010 143
cert_ridgeSupport_suffix_decode_2 704 008 12 207 32 015 009 175
cert_ridgeSupport_suffix_decode_2 704 007 12 239 32 015 008 207
cert_ridgeSupport_suffix_decode_2 704 006 12 271 32 015 007 239
cert_ridgeSupport_suffix_decode_2 704 005 12 303 32 015 006 271
cert_ridgeSupport_suffix_decode_2 704 004 12 335 32 015 005 303
cert_ridgeSupport_suffix_decode_2 704 003 12 367 32 015 004 335
cert_ridgeSupport_suffix_decode_2 704 002 12 399 32 015 003 367
cert_ridgeSupport_suffix_decode_2 704 001 12 431 32 015 002 399
cert_ridgeSupport_suffix_decode_2 704 000 12 463 32 015 001 431
cert_ridgeSupport_eq 704
theorem ridgeTest_large_704 : ridgeTest 704 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask, ridgeSupport704_010_mask, ridgeSupport704_011_mask, ridgeSupport704_012_mask, ridgeSupport704_013_mask, ridgeSupport704_014_mask]
    decide +kernel
  · rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, ridgeSupport704_010_checked, ridgeSupport704_011_checked, ridgeSupport704_012_checked, ridgeSupport704_013_checked, ridgeSupport704_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase04
