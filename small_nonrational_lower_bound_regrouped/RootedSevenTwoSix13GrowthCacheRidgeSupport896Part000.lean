module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheRidgeSupport896Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport896_000_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_000 =
      (ridgeSupport896_000, ridgeSupport896_rest_001) := by decide +kernel
theorem ridgeSupport896_000_mask : RawNatGrowthCheck.mask ridgeSupport896_000 = (certNat% 0) := by decide +kernel
theorem ridgeSupport896_000_checked :
    (ridgeSupport896_000.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_001_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_001 =
      (ridgeSupport896_001, ridgeSupport896_rest_002) := by decide +kernel
theorem ridgeSupport896_001_mask : RawNatGrowthCheck.mask ridgeSupport896_001 = (certNat% 1) := by decide +kernel
theorem ridgeSupport896_001_checked :
    (ridgeSupport896_001.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_002_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_002 =
      (ridgeSupport896_002, ridgeSupport896_rest_003) := by decide +kernel
theorem ridgeSupport896_002_mask : RawNatGrowthCheck.mask ridgeSupport896_002 = (certNat% 2) := by decide +kernel
theorem ridgeSupport896_002_checked :
    (ridgeSupport896_002.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_003_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_003 =
      (ridgeSupport896_003, ridgeSupport896_rest_004) := by decide +kernel
theorem ridgeSupport896_003_mask : RawNatGrowthCheck.mask ridgeSupport896_003 = (certNat% 3) := by decide +kernel
theorem ridgeSupport896_003_checked :
    (ridgeSupport896_003.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_004_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_004 =
      (ridgeSupport896_004, ridgeSupport896_rest_005) := by decide +kernel
theorem ridgeSupport896_004_mask : RawNatGrowthCheck.mask ridgeSupport896_004 = (certNat% 4) := by decide +kernel
theorem ridgeSupport896_004_checked :
    (ridgeSupport896_004.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_005_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_005 =
      (ridgeSupport896_005, ridgeSupport896_rest_006) := by decide +kernel
theorem ridgeSupport896_005_mask : RawNatGrowthCheck.mask ridgeSupport896_005 = (certNat% 5) := by decide +kernel
theorem ridgeSupport896_005_checked :
    (ridgeSupport896_005.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_006_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_006 =
      (ridgeSupport896_006, ridgeSupport896_rest_007) := by decide +kernel
theorem ridgeSupport896_006_mask : RawNatGrowthCheck.mask ridgeSupport896_006 = (certNat% 6) := by decide +kernel
theorem ridgeSupport896_006_checked :
    (ridgeSupport896_006.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_007_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_007 =
      (ridgeSupport896_007, ridgeSupport896_rest_008) := by decide +kernel
theorem ridgeSupport896_007_mask : RawNatGrowthCheck.mask ridgeSupport896_007 = (certNat% 7) := by decide +kernel
theorem ridgeSupport896_007_checked :
    (ridgeSupport896_007.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
