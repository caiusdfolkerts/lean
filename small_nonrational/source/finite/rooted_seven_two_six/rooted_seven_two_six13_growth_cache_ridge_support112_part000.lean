module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport112Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport112_000_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_000 =
      (ridgeSupport112_000, ridgeSupport112_rest_001) := by decide +kernel
theorem ridgeSupport112_000_mask : RawNatGrowthCheck.mask ridgeSupport112_000 = 0x3fffffff80000000000000000000000000000000000000000000000000000000000000000000000000001 := by decide +kernel
theorem ridgeSupport112_000_checked :
    (ridgeSupport112_000.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_001_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_001 =
      (ridgeSupport112_001, ridgeSupport112_rest_002) := by decide +kernel
theorem ridgeSupport112_001_mask : RawNatGrowthCheck.mask ridgeSupport112_001 = 0x1ffffffc0000000000000000000000000000000000000000000000000000000000000000000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport112_001_checked :
    (ridgeSupport112_001.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_002_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_002 =
      (ridgeSupport112_002, ridgeSupport112_rest_003) := by decide +kernel
theorem ridgeSupport112_002_mask : RawNatGrowthCheck.mask ridgeSupport112_002 = 0x1fffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport112_002_checked :
    (ridgeSupport112_002.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_003_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_003 =
      (ridgeSupport112_003, ridgeSupport112_rest_004) := by decide +kernel
theorem ridgeSupport112_003_mask : RawNatGrowthCheck.mask ridgeSupport112_003 = 0x1ffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport112_003_checked :
    (ridgeSupport112_003.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_004_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_004 =
      (ridgeSupport112_004, ridgeSupport112_rest_005) := by decide +kernel
theorem ridgeSupport112_004_mask : RawNatGrowthCheck.mask ridgeSupport112_004 = 0x1fffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport112_004_checked :
    (ridgeSupport112_004.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_005_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_005 =
      (ridgeSupport112_005, ridgeSupport112_rest_006) := by decide +kernel
theorem ridgeSupport112_005_mask : RawNatGrowthCheck.mask ridgeSupport112_005 = 0x1fffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport112_005_checked :
    (ridgeSupport112_005.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_006_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_006 =
      (ridgeSupport112_006, ridgeSupport112_rest_007) := by decide +kernel
theorem ridgeSupport112_006_mask : RawNatGrowthCheck.mask ridgeSupport112_006 = 0x100000000000000000000000000000000000000000000000003f00003fffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport112_006_checked :
    (ridgeSupport112_006.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel
theorem ridgeSupport112_007_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport112_rest_007 =
      (ridgeSupport112_007, ridgeSupport112_rest_008) := by decide +kernel
theorem ridgeSupport112_007_mask : RawNatGrowthCheck.mask ridgeSupport112_007 = 0x1fffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport112_007_checked :
    (ridgeSupport112_007.all (fun c => hasNat (rawCells c).ridgeMasks 112)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
