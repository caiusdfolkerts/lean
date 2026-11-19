module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheRidgeSupport832Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport832_008_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport832_rest_008 =
      (ridgeSupport832_008, ridgeSupport832_rest_009) := by decide +kernel
theorem ridgeSupport832_008_mask : RawNatGrowthCheck.mask ridgeSupport832_008 = (certNat% 0) := by decide +kernel
theorem ridgeSupport832_008_checked :
    (ridgeSupport832_008.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_009_decode :
    PackedRawNatGrowth.readList 11 3 ridgeSupport832_rest_009 =
      (ridgeSupport832_009, ridgeSupport832_rest_010) := by decide +kernel
theorem ridgeSupport832_009_mask : RawNatGrowthCheck.mask ridgeSupport832_009 = (certNat% 1) := by decide +kernel
theorem ridgeSupport832_009_checked :
    (ridgeSupport832_009.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
