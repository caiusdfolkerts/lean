module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheRidgeSupport112Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport112_008_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_008 =
      (ridgeSupport112_008, ridgeSupport112_rest_009) := by decide +kernel
theorem ridgeSupport112_008_mask : RawNatGrowthCheck.mask ridgeSupport112_008 = (certNat% 0) := by decide +kernel
theorem ridgeSupport112_008_checked :
    (ridgeSupport112_008.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_009_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_009 =
      (ridgeSupport112_009, ridgeSupport112_rest_010) := by decide +kernel
theorem ridgeSupport112_009_mask : RawNatGrowthCheck.mask ridgeSupport112_009 = (certNat% 1) := by decide +kernel
theorem ridgeSupport112_009_checked :
    (ridgeSupport112_009.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_010_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_010 =
      (ridgeSupport112_010, ridgeSupport112_rest_011) := by decide +kernel
theorem ridgeSupport112_010_mask : RawNatGrowthCheck.mask ridgeSupport112_010 = (certNat% 2) := by decide +kernel
theorem ridgeSupport112_010_checked :
    (ridgeSupport112_010.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_011_decode :
    PackedRawNatGrowth.readList 11 21 ridgeSupport112_rest_011 =
      (ridgeSupport112_011, ridgeSupport112_rest_012) := by decide +kernel
theorem ridgeSupport112_011_mask : RawNatGrowthCheck.mask ridgeSupport112_011 = (certNat% 3) := by decide +kernel
theorem ridgeSupport112_011_checked :
    (ridgeSupport112_011.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
