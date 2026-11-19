module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheRidgeSupport7Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport7_000_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport7_rest_000 =
      (ridgeSupport7_000, ridgeSupport7_rest_001) := by decide +kernel
theorem ridgeSupport7_000_mask : RawNatGrowthCheck.mask ridgeSupport7_000 = 0xffffffff := by decide +kernel
theorem ridgeSupport7_000_checked :
    (ridgeSupport7_000.all (fun c => hasNat (rawCells c).ridgeMasks 7)) = true := by decide +kernel
theorem ridgeSupport7_001_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport7_rest_001 =
      (ridgeSupport7_001, ridgeSupport7_rest_002) := by decide +kernel
theorem ridgeSupport7_001_mask : RawNatGrowthCheck.mask ridgeSupport7_001 = (certNat% 0) := by decide +kernel
theorem ridgeSupport7_001_checked :
    (ridgeSupport7_001.all (fun c => hasNat (rawCells c).ridgeMasks 7)) = true := by decide +kernel
theorem ridgeSupport7_002_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport7_rest_002 =
      (ridgeSupport7_002, ridgeSupport7_rest_003) := by decide +kernel
theorem ridgeSupport7_002_mask : RawNatGrowthCheck.mask ridgeSupport7_002 = (certNat% 1) := by decide +kernel
theorem ridgeSupport7_002_checked :
    (ridgeSupport7_002.all (fun c => hasNat (rawCells c).ridgeMasks 7)) = true := by decide +kernel
theorem ridgeSupport7_003_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport7_rest_003 =
      (ridgeSupport7_003, ridgeSupport7_rest_004) := by decide +kernel
theorem ridgeSupport7_003_mask : RawNatGrowthCheck.mask ridgeSupport7_003 = (certNat% 2) := by decide +kernel
theorem ridgeSupport7_003_checked :
    (ridgeSupport7_003.all (fun c => hasNat (rawCells c).ridgeMasks 7)) = true := by decide +kernel
theorem ridgeSupport7_004_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport7_rest_004 =
      (ridgeSupport7_004, ridgeSupport7_rest_005) := by decide +kernel
theorem ridgeSupport7_004_mask : RawNatGrowthCheck.mask ridgeSupport7_004 = (certNat% 3) := by decide +kernel
theorem ridgeSupport7_004_checked :
    (ridgeSupport7_004.all (fun c => hasNat (rawCells c).ridgeMasks 7)) = true := by decide +kernel
theorem ridgeSupport7_005_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport7_rest_005 =
      (ridgeSupport7_005, ridgeSupport7_rest_006) := by decide +kernel
theorem ridgeSupport7_005_mask : RawNatGrowthCheck.mask ridgeSupport7_005 = (certNat% 4) := by decide +kernel
theorem ridgeSupport7_005_checked :
    (ridgeSupport7_005.all (fun c => hasNat (rawCells c).ridgeMasks 7)) = true := by decide +kernel
theorem ridgeSupport7_006_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport7_rest_006 =
      (ridgeSupport7_006, ridgeSupport7_rest_007) := by decide +kernel
theorem ridgeSupport7_006_mask : RawNatGrowthCheck.mask ridgeSupport7_006 = (certNat% 5) := by decide +kernel
theorem ridgeSupport7_006_checked :
    (ridgeSupport7_006.all (fun c => hasNat (rawCells c).ridgeMasks 7)) = true := by decide +kernel
theorem ridgeSupport7_007_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport7_rest_007 =
      (ridgeSupport7_007, ridgeSupport7_rest_008) := by decide +kernel
theorem ridgeSupport7_007_mask : RawNatGrowthCheck.mask ridgeSupport7_007 = (certNat% 6) := by decide +kernel
theorem ridgeSupport7_007_checked :
    (ridgeSupport7_007.all (fun c => hasNat (rawCells c).ridgeMasks 7)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
