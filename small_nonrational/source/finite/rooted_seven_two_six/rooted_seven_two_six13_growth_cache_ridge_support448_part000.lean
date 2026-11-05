module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport448Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport448_000_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport448_rest_000 =
      (ridgeSupport448_000, ridgeSupport448_rest_001) := by decide +kernel
theorem ridgeSupport448_000_mask : RawNatGrowthCheck.mask ridgeSupport448_000 = 0x1a3000000000006078b468c0000000000181e00000000000c0f0000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_000_checked :
    (ridgeSupport448_000.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_001_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport448_rest_001 =
      (ridgeSupport448_001, ridgeSupport448_rest_002) := by decide +kernel
theorem ridgeSupport448_001_mask : RawNatGrowthCheck.mask ridgeSupport448_001 = 0x15d40005e85e80000000000000000005a3462d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_001_checked :
    (ridgeSupport448_001.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_002_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport448_rest_002 =
      (ridgeSupport448_002, ridgeSupport448_rest_003) := by decide +kernel
theorem ridgeSupport448_002_mask : RawNatGrowthCheck.mask ridgeSupport448_002 = 0x70035d40005e85eb0d700200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_002_checked :
    (ridgeSupport448_002.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_003_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport448_rest_003 =
      (ridgeSupport448_003, ridgeSupport448_rest_004) := by decide +kernel
theorem ridgeSupport448_003_mask : RawNatGrowthCheck.mask ridgeSupport448_003 = 0x10d70035d40005e85eb0d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_003_checked :
    (ridgeSupport448_003.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_004_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport448_rest_004 =
      (ridgeSupport448_004, ridgeSupport448_rest_005) := by decide +kernel
theorem ridgeSupport448_004_mask : RawNatGrowthCheck.mask ridgeSupport448_004 = 0x68a2803cf000000000d70d70000e800000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_004_checked :
    (ridgeSupport448_004.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_005_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport448_rest_005 =
      (ridgeSupport448_005, ridgeSupport448_rest_006) := by decide +kernel
theorem ridgeSupport448_005_mask : RawNatGrowthCheck.mask ridgeSupport448_005 = 0x70000e8a2803cf000000000d70d700008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_005_checked :
    (ridgeSupport448_005.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_006_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport448_rest_006 =
      (ridgeSupport448_006, ridgeSupport448_rest_007) := by decide +kernel
theorem ridgeSupport448_006_mask : RawNatGrowthCheck.mask ridgeSupport448_006 = 0x102b0000000000000000000000030c3000a2803cf000000000d70d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_006_checked :
    (ridgeSupport448_006.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_007_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport448_rest_007 =
      (ridgeSupport448_007, ridgeSupport448_rest_008) := by decide +kernel
theorem ridgeSupport448_007_mask : RawNatGrowthCheck.mask ridgeSupport448_007 = 0x1000000c300002b02b0030c0000ac0ac00c300002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_007_checked :
    (ridgeSupport448_007.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
