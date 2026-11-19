module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05GrowthCacheRidgeSupport832Part000
public import RootedSixExtra05GrowthCacheRidgeSupport832Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 832 012 12
cert_ridgeSupport_suffix_decode_4 832 011 12 9 9 012 012 0
cert_ridgeSupport_suffix_decode_4 832 010 12 41 32 012 011 9
cert_ridgeSupport_suffix_decode_4 832 009 12 73 32 012 010 41
cert_ridgeSupport_suffix_decode_4 832 008 12 105 32 012 009 73
cert_ridgeSupport_suffix_decode_4 832 007 12 137 32 012 008 105
cert_ridgeSupport_suffix_decode_4 832 006 12 169 32 012 007 137
cert_ridgeSupport_suffix_decode_4 832 005 12 201 32 012 006 169
cert_ridgeSupport_suffix_decode_4 832 004 12 233 32 012 005 201
cert_ridgeSupport_suffix_decode_4 832 003 12 265 32 012 004 233
cert_ridgeSupport_suffix_decode_4 832 002 12 297 32 012 003 265
cert_ridgeSupport_suffix_decode_4 832 001 12 329 32 012 002 297
cert_ridgeSupport_suffix_decode_4 832 000 12 361 32 012 001 329
cert_ridgeSupport_eq_4 832
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask, ridgeSupport832_010_mask, ridgeSupport832_011_mask]
    decide +kernel
  · rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, ridgeSupport832_010_checked, ridgeSupport832_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
