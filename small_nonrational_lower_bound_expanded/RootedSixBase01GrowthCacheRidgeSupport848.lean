module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport848PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 848 009 14
cert_ridgeSupport_suffix_decode_2 848 008 14 5 5 009 009 0
cert_ridgeSupport_suffix_decode_2 848 007 14 37 32 009 008 5
cert_ridgeSupport_suffix_decode_2 848 006 14 69 32 009 007 37
cert_ridgeSupport_suffix_decode_2 848 005 14 101 32 009 006 69
cert_ridgeSupport_suffix_decode_2 848 004 14 133 32 009 005 101
cert_ridgeSupport_suffix_decode_2 848 003 14 165 32 009 004 133
cert_ridgeSupport_suffix_decode_2 848 002 14 197 32 009 003 165
cert_ridgeSupport_suffix_decode_2 848 001 14 229 32 009 002 197
cert_ridgeSupport_suffix_decode_2 848 000 14 261 32 009 001 229
cert_ridgeSupport_eq_3 848
theorem ridgeTest_large_848 : ridgeTest 848 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport848_eq]
    simp only [ridgeSupport848_suffix_000, ridgeSupport848_suffix_001, ridgeSupport848_suffix_002, ridgeSupport848_suffix_003, ridgeSupport848_suffix_004, ridgeSupport848_suffix_005, ridgeSupport848_suffix_006, ridgeSupport848_suffix_007, ridgeSupport848_suffix_008, ridgeSupport848_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport848_000_mask, ridgeSupport848_001_mask, ridgeSupport848_002_mask, ridgeSupport848_003_mask, ridgeSupport848_004_mask, ridgeSupport848_005_mask, ridgeSupport848_006_mask, ridgeSupport848_007_mask, ridgeSupport848_008_mask]
    decide +kernel
  · rw [ridgeSupport848_eq]
    simp only [ridgeSupport848_suffix_000, ridgeSupport848_suffix_001, ridgeSupport848_suffix_002, ridgeSupport848_suffix_003, ridgeSupport848_suffix_004, ridgeSupport848_suffix_005, ridgeSupport848_suffix_006, ridgeSupport848_suffix_007, ridgeSupport848_suffix_008, ridgeSupport848_suffix_009, List.all_append, List.all_nil, ridgeSupport848_000_checked, ridgeSupport848_001_checked, ridgeSupport848_002_checked, ridgeSupport848_003_checked, ridgeSupport848_004_checked, ridgeSupport848_005_checked, ridgeSupport848_006_checked, ridgeSupport848_007_checked, ridgeSupport848_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
