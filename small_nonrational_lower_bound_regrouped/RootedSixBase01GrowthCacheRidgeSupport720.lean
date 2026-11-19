module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport720PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 720 009 14
cert_ridgeSupport_suffix_decode_2 720 008 14 5 5 009 009 0
cert_ridgeSupport_suffix_decode_2 720 007 14 37 32 009 008 5
cert_ridgeSupport_suffix_decode_2 720 006 14 69 32 009 007 37
cert_ridgeSupport_suffix_decode_2 720 005 14 101 32 009 006 69
cert_ridgeSupport_suffix_decode_2 720 004 14 133 32 009 005 101
cert_ridgeSupport_suffix_decode_2 720 003 14 165 32 009 004 133
cert_ridgeSupport_suffix_decode_2 720 002 14 197 32 009 003 165
cert_ridgeSupport_suffix_decode_2 720 001 14 229 32 009 002 197
cert_ridgeSupport_suffix_decode_2 720 000 14 261 32 009 001 229
cert_ridgeSupport_eq_3 720
theorem ridgeTest_large_720 : ridgeTest 720 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport720_eq]
    simp only [ridgeSupport720_suffix_000, ridgeSupport720_suffix_001, ridgeSupport720_suffix_002, ridgeSupport720_suffix_003, ridgeSupport720_suffix_004, ridgeSupport720_suffix_005, ridgeSupport720_suffix_006, ridgeSupport720_suffix_007, ridgeSupport720_suffix_008, ridgeSupport720_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport720_000_mask, ridgeSupport720_001_mask, ridgeSupport720_002_mask, ridgeSupport720_003_mask, ridgeSupport720_004_mask, ridgeSupport720_005_mask, ridgeSupport720_006_mask, ridgeSupport720_007_mask, ridgeSupport720_008_mask]
    decide +kernel
  · rw [ridgeSupport720_eq]
    simp only [ridgeSupport720_suffix_000, ridgeSupport720_suffix_001, ridgeSupport720_suffix_002, ridgeSupport720_suffix_003, ridgeSupport720_suffix_004, ridgeSupport720_suffix_005, ridgeSupport720_suffix_006, ridgeSupport720_suffix_007, ridgeSupport720_suffix_008, ridgeSupport720_suffix_009, List.all_append, List.all_nil, ridgeSupport720_000_checked, ridgeSupport720_001_checked, ridgeSupport720_002_checked, ridgeSupport720_003_checked, ridgeSupport720_004_checked, ridgeSupport720_005_checked, ridgeSupport720_006_checked, ridgeSupport720_007_checked, ridgeSupport720_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
