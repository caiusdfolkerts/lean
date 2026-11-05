module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport704Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport704_000_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport704_rest_000 =
      (ridgeSupport704_000, ridgeSupport704_rest_001) := by decide +kernel
theorem ridgeSupport704_000_mask : RawNatGrowthCheck.mask ridgeSupport704_000 = 0x155000000006078002585540000000181e00000000000c0f0000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_000_checked :
    (ridgeSupport704_000.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_001_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport704_rest_001 =
      (ridgeSupport704_001, ridgeSupport704_rest_002) := by decide +kernel
theorem ridgeSupport704_001_mask : RawNatGrowthCheck.mask ridgeSupport704_001 = 0xe780012b52b40000000000000000012c2aa960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_001_checked :
    (ridgeSupport704_001.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_002_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport704_rest_002 =
      (ridgeSupport704_002, ridgeSupport704_rest_003) := by decide +kernel
theorem ridgeSupport704_002_mask : RawNatGrowthCheck.mask ridgeSupport704_002 = 0x8c01e780012b52b4c78c0100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_002_checked :
    (ridgeSupport704_002.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_003_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport704_rest_003 =
      (ridgeSupport704_003, ridgeSupport704_rest_004) := by decide +kernel
theorem ridgeSupport704_003_mask : RawNatGrowthCheck.mask ridgeSupport704_003 = 0x478c01e780012b52b4c7000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_003_checked :
    (ridgeSupport704_003.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_004_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport704_rest_004 =
      (ridgeSupport704_004, ridgeSupport704_rest_005) := by decide +kernel
theorem ridgeSupport704_004_mask : RawNatGrowthCheck.mask ridgeSupport704_004 = 0x361840cf300000000078c78c000b400000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_004_checked :
    (ridgeSupport704_004.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_005_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport704_rest_005 =
      (ridgeSupport704_005, ridgeSupport704_rest_006) := by decide +kernel
theorem ridgeSupport704_005_mask : RawNatGrowthCheck.mask ridgeSupport704_005 = 0x8c000b61840cf300000000078c78c0008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_005_checked :
    (ridgeSupport704_005.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_006_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport704_rest_006 =
      (ridgeSupport704_006, ridgeSupport704_rest_007) := by decide +kernel
theorem ridgeSupport704_006_mask : RawNatGrowthCheck.mask ridgeSupport704_006 = 0x484c00000000000000000000000c30c021840cf300000000078c7000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_006_checked :
    (ridgeSupport704_006.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_007_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport704_rest_007 =
      (ridgeSupport704_007, ridgeSupport704_rest_008) := by decide +kernel
theorem ridgeSupport704_007_mask : RawNatGrowthCheck.mask ridgeSupport704_007 = 0x200000030c00084c84c00c30002132130030c0008480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_007_checked :
    (ridgeSupport704_007.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
