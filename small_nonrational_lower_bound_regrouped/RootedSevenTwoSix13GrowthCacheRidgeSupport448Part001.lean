module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheRidgeSupport448Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport448_008_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport448_rest_008 =
      (ridgeSupport448_008, ridgeSupport448_rest_009) := by decide +kernel
theorem ridgeSupport448_008_mask : RawNatGrowthCheck.mask ridgeSupport448_008 = (certNat% 0) := by decide +kernel
theorem ridgeSupport448_008_checked :
    (ridgeSupport448_008.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_009_decode :
    PackedRawNatGrowth.readList 11 3 ridgeSupport448_rest_009 =
      (ridgeSupport448_009, ridgeSupport448_rest_010) := by decide +kernel
theorem ridgeSupport448_009_mask : RawNatGrowthCheck.mask ridgeSupport448_009 = (certNat% 1) := by decide +kernel
theorem ridgeSupport448_009_checked :
    (ridgeSupport448_009.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
