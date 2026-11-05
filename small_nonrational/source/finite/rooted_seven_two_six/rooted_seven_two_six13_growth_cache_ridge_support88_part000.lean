module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport88Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport88_000_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_000 =
      (ridgeSupport88_000, ridgeSupport88_rest_001) := by decide +kernel
theorem ridgeSupport88_000_mask : RawNatGrowthCheck.mask ridgeSupport88_000 = 0x7fffffff0000000000000000000000000000000000000000001 := by decide +kernel
theorem ridgeSupport88_000_checked :
    (ridgeSupport88_000.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_001_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_001 =
      (ridgeSupport88_001, ridgeSupport88_rest_002) := by decide +kernel
theorem ridgeSupport88_001_mask : RawNatGrowthCheck.mask ridgeSupport88_001 = 0x1ffffffc0000000000000000000000000000000000000000000000000000000000000000000f800000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport88_001_checked :
    (ridgeSupport88_001.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_002_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_002 =
      (ridgeSupport88_002, ridgeSupport88_rest_003) := by decide +kernel
theorem ridgeSupport88_002_mask : RawNatGrowthCheck.mask ridgeSupport88_002 = 0x1fffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport88_002_checked :
    (ridgeSupport88_002.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_003_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_003 =
      (ridgeSupport88_003, ridgeSupport88_rest_004) := by decide +kernel
theorem ridgeSupport88_003_mask : RawNatGrowthCheck.mask ridgeSupport88_003 = 0x1ffffc000000000000000000000000000000000000000000000000000000000000000000000000000000003ffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport88_003_checked :
    (ridgeSupport88_003.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_004_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_004 =
      (ridgeSupport88_004, ridgeSupport88_rest_005) := by decide +kernel
theorem ridgeSupport88_004_mask : RawNatGrowthCheck.mask ridgeSupport88_004 = 0x1fffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport88_004_checked :
    (ridgeSupport88_004.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_005_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_005 =
      (ridgeSupport88_005, ridgeSupport88_rest_006) := by decide +kernel
theorem ridgeSupport88_005_mask : RawNatGrowthCheck.mask ridgeSupport88_005 = 0x1fffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport88_005_checked :
    (ridgeSupport88_005.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_006_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_006 =
      (ridgeSupport88_006, ridgeSupport88_rest_007) := by decide +kernel
theorem ridgeSupport88_006_mask : RawNatGrowthCheck.mask ridgeSupport88_006 = 0x100000000000000000000000003f00000000000000000000000000000000000000000000000000000003fffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport88_006_checked :
    (ridgeSupport88_006.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel
theorem ridgeSupport88_007_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport88_rest_007 =
      (ridgeSupport88_007, ridgeSupport88_rest_008) := by decide +kernel
theorem ridgeSupport88_007_mask : RawNatGrowthCheck.mask ridgeSupport88_007 = 0x1fffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport88_007_checked :
    (ridgeSupport88_007.all (fun c => hasNat (rawCells c).ridgeMasks 88)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
