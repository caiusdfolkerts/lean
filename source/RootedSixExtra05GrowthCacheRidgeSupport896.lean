module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05GrowthCacheRidgeSupport896Part000
public import RootedSixExtra05GrowthCacheRidgeSupport896Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 896 012 12
cert_ridgeSupport_suffix_decode_4 896 011 12 9 9 012 012 0
cert_ridgeSupport_suffix_decode_4 896 010 12 41 32 012 011 9
cert_ridgeSupport_suffix_decode_4 896 009 12 73 32 012 010 41
cert_ridgeSupport_suffix_decode_4 896 008 12 105 32 012 009 73
cert_ridgeSupport_suffix_decode_4 896 007 12 137 32 012 008 105
cert_ridgeSupport_suffix_decode_4 896 006 12 169 32 012 007 137
cert_ridgeSupport_suffix_decode_4 896 005 12 201 32 012 006 169
cert_ridgeSupport_suffix_decode_4 896 004 12 233 32 012 005 201
cert_ridgeSupport_suffix_decode_4 896 003 12 265 32 012 004 233
cert_ridgeSupport_suffix_decode_4 896 002 12 297 32 012 003 265
cert_ridgeSupport_suffix_decode_4 896 001 12 329 32 012 002 297
cert_ridgeSupport_suffix_decode_4 896 000 12 361 32 012 001 329
cert_ridgeSupport_eq_4 896
theorem ridgeTest_large_896 : ridgeTest 896 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport896_000_mask, ridgeSupport896_001_mask, ridgeSupport896_002_mask, ridgeSupport896_003_mask, ridgeSupport896_004_mask, ridgeSupport896_005_mask, ridgeSupport896_006_mask, ridgeSupport896_007_mask, ridgeSupport896_008_mask, ridgeSupport896_009_mask, ridgeSupport896_010_mask, ridgeSupport896_011_mask]
    decide +kernel
  · rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, List.all_append, List.all_nil, ridgeSupport896_000_checked, ridgeSupport896_001_checked, ridgeSupport896_002_checked, ridgeSupport896_003_checked, ridgeSupport896_004_checked, ridgeSupport896_005_checked, ridgeSupport896_006_checked, ridgeSupport896_007_checked, ridgeSupport896_008_checked, ridgeSupport896_009_checked, ridgeSupport896_010_checked, ridgeSupport896_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
