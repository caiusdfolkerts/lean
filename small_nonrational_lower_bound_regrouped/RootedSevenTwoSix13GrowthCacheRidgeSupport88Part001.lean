module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheRidgeSupport88Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport88_008_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_008 =
      (ridgeSupport88_008, ridgeSupport88_rest_009) := by decide +kernel
theorem ridgeSupport88_008_mask : RawNatGrowthCheck.mask ridgeSupport88_008 = (certNat% 0) := by decide +kernel
theorem ridgeSupport88_008_checked :
    (ridgeSupport88_008.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_009_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_009 =
      (ridgeSupport88_009, ridgeSupport88_rest_010) := by decide +kernel
theorem ridgeSupport88_009_mask : RawNatGrowthCheck.mask ridgeSupport88_009 = (certNat% 1) := by decide +kernel
theorem ridgeSupport88_009_checked :
    (ridgeSupport88_009.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_010_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_010 =
      (ridgeSupport88_010, ridgeSupport88_rest_011) := by decide +kernel
theorem ridgeSupport88_010_mask : RawNatGrowthCheck.mask ridgeSupport88_010 = (certNat% 2) := by decide +kernel
theorem ridgeSupport88_010_checked :
    (ridgeSupport88_010.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_011_decode :
    PackedRawNatGrowth.readList 11 21 ridgeSupport88_rest_011 =
      (ridgeSupport88_011, ridgeSupport88_rest_012) := by decide +kernel
theorem ridgeSupport88_011_mask : RawNatGrowthCheck.mask ridgeSupport88_011 = (certNat% 3) := by decide +kernel
theorem ridgeSupport88_011_checked :
    (ridgeSupport88_011.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
