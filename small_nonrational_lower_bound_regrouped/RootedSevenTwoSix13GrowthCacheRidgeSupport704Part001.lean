module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheRidgeSupport704Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport704_008_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport704_rest_008 =
      (ridgeSupport704_008, ridgeSupport704_rest_009) := by decide +kernel
theorem ridgeSupport704_008_mask : RawNatGrowthCheck.mask ridgeSupport704_008 = (certNat% 0) := by decide +kernel
theorem ridgeSupport704_008_checked :
    (ridgeSupport704_008.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_009_decode :
    PackedRawNatGrowth.readList 11 3 ridgeSupport704_rest_009 =
      (ridgeSupport704_009, ridgeSupport704_rest_010) := by decide +kernel
theorem ridgeSupport704_009_mask : RawNatGrowthCheck.mask ridgeSupport704_009 = (certNat% 1) := by decide +kernel
theorem ridgeSupport704_009_checked :
    (ridgeSupport704_009.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
