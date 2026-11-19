module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05GrowthCacheRidgeSupport448Part000
public import RootedSixExtra05GrowthCacheRidgeSupport448Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 448 012 12
cert_ridgeSupport_suffix_decode_4 448 011 12 9 9 012 012 0
cert_ridgeSupport_suffix_decode_4 448 010 12 41 32 012 011 9
cert_ridgeSupport_suffix_decode_4 448 009 12 73 32 012 010 41
cert_ridgeSupport_suffix_decode_4 448 008 12 105 32 012 009 73
cert_ridgeSupport_suffix_decode_4 448 007 12 137 32 012 008 105
cert_ridgeSupport_suffix_decode_4 448 006 12 169 32 012 007 137
cert_ridgeSupport_suffix_decode_4 448 005 12 201 32 012 006 169
cert_ridgeSupport_suffix_decode_4 448 004 12 233 32 012 005 201
cert_ridgeSupport_suffix_decode_4 448 003 12 265 32 012 004 233
cert_ridgeSupport_suffix_decode_4 448 002 12 297 32 012 003 265
cert_ridgeSupport_suffix_decode_4 448 001 12 329 32 012 002 297
cert_ridgeSupport_suffix_decode_4 448 000 12 361 32 012 001 329
cert_ridgeSupport_eq_4 448
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask]
    decide +kernel
  · rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
