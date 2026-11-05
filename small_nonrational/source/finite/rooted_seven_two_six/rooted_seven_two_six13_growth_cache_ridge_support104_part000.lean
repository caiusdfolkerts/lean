module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport104Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport104_000_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport104_rest_000 =
      (ridgeSupport104_000, ridgeSupport104_rest_001) := by decide +kernel
theorem ridgeSupport104_000_mask : RawNatGrowthCheck.mask ridgeSupport104_000 = 0xfffffffe000000000000000000000000000000000000000000000000000000001 := by decide +kernel
theorem ridgeSupport104_000_checked :
    (ridgeSupport104_000.all (fun c => hasNat (rawCells c).ridgeMasks 104)) = true := by decide +kernel
theorem ridgeSupport104_001_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport104_rest_001 =
      (ridgeSupport104_001, ridgeSupport104_rest_002) := by decide +kernel
theorem ridgeSupport104_001_mask : RawNatGrowthCheck.mask ridgeSupport104_001 = 0x1ffffffc00000000000000000000000000000000000000000000000000000000000000000000001f00000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport104_001_checked :
    (ridgeSupport104_001.all (fun c => hasNat (rawCells c).ridgeMasks 104)) = true := by decide +kernel
theorem ridgeSupport104_002_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport104_rest_002 =
      (ridgeSupport104_002, ridgeSupport104_rest_003) := by decide +kernel
theorem ridgeSupport104_002_mask : RawNatGrowthCheck.mask ridgeSupport104_002 = 0x1fffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport104_002_checked :
    (ridgeSupport104_002.all (fun c => hasNat (rawCells c).ridgeMasks 104)) = true := by decide +kernel
theorem ridgeSupport104_003_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport104_rest_003 =
      (ridgeSupport104_003, ridgeSupport104_rest_004) := by decide +kernel
theorem ridgeSupport104_003_mask : RawNatGrowthCheck.mask ridgeSupport104_003 = 0x1ffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport104_003_checked :
    (ridgeSupport104_003.all (fun c => hasNat (rawCells c).ridgeMasks 104)) = true := by decide +kernel
theorem ridgeSupport104_004_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport104_rest_004 =
      (ridgeSupport104_004, ridgeSupport104_rest_005) := by decide +kernel
theorem ridgeSupport104_004_mask : RawNatGrowthCheck.mask ridgeSupport104_004 = 0x1fffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport104_004_checked :
    (ridgeSupport104_004.all (fun c => hasNat (rawCells c).ridgeMasks 104)) = true := by decide +kernel
theorem ridgeSupport104_005_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport104_rest_005 =
      (ridgeSupport104_005, ridgeSupport104_rest_006) := by decide +kernel
theorem ridgeSupport104_005_mask : RawNatGrowthCheck.mask ridgeSupport104_005 = 0x1fffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport104_005_checked :
    (ridgeSupport104_005.all (fun c => hasNat (rawCells c).ridgeMasks 104)) = true := by decide +kernel
theorem ridgeSupport104_006_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport104_rest_006 =
      (ridgeSupport104_006, ridgeSupport104_rest_007) := by decide +kernel
theorem ridgeSupport104_006_mask : RawNatGrowthCheck.mask ridgeSupport104_006 = 0x40000000000000000000000000000000000000fc000000000000000000000000000003fffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport104_006_checked :
    (ridgeSupport104_006.all (fun c => hasNat (rawCells c).ridgeMasks 104)) = true := by decide +kernel
theorem ridgeSupport104_007_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport104_rest_007 =
      (ridgeSupport104_007, ridgeSupport104_rest_008) := by decide +kernel
theorem ridgeSupport104_007_mask : RawNatGrowthCheck.mask ridgeSupport104_007 = 0x7fffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport104_007_checked :
    (ridgeSupport104_007.all (fun c => hasNat (rawCells c).ridgeMasks 104)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
