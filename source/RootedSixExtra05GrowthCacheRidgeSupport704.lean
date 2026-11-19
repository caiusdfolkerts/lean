module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05GrowthCacheRidgeSupport704Part000
public import RootedSixExtra05GrowthCacheRidgeSupport704Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 704 012 12
cert_ridgeSupport_suffix_decode_4 704 011 12 9 9 012 012 0
cert_ridgeSupport_suffix_decode_4 704 010 12 41 32 012 011 9
cert_ridgeSupport_suffix_decode_4 704 009 12 73 32 012 010 41
cert_ridgeSupport_suffix_decode_4 704 008 12 105 32 012 009 73
cert_ridgeSupport_suffix_decode_4 704 007 12 137 32 012 008 105
cert_ridgeSupport_suffix_decode_4 704 006 12 169 32 012 007 137
cert_ridgeSupport_suffix_decode_4 704 005 12 201 32 012 006 169
cert_ridgeSupport_suffix_decode_4 704 004 12 233 32 012 005 201
cert_ridgeSupport_suffix_decode_4 704 003 12 265 32 012 004 233
cert_ridgeSupport_suffix_decode_4 704 002 12 297 32 012 003 265
cert_ridgeSupport_suffix_decode_4 704 001 12 329 32 012 002 297
cert_ridgeSupport_suffix_decode_4 704 000 12 361 32 012 001 329
cert_ridgeSupport_eq_4 704
theorem ridgeTest_large_704 : ridgeTest 704 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask, ridgeSupport704_010_mask, ridgeSupport704_011_mask]
    decide +kernel
  · rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, ridgeSupport704_010_checked, ridgeSupport704_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
