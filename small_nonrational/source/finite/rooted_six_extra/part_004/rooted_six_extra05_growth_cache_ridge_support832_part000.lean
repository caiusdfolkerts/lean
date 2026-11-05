module
prelude
public import RootedSixExtra05GrowthCacheRidgeSupport832Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport832_000_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_000 =
      (ridgeSupport832_000, ridgeSupport832_rest_001) := by decide +kernel
theorem ridgeSupport832_000_mask : RawNatGrowthCheck.mask ridgeSupport832_000 = 0x40000000000000007e00fc00000000000000007e00fc00000000000000000000000000000a200800008020002000000 := by decide +kernel
theorem ridgeSupport832_000_checked :
    (ridgeSupport832_000.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_001_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_001 =
      (ridgeSupport832_001, ridgeSupport832_rest_002) := by decide +kernel
theorem ridgeSupport832_001_mask : RawNatGrowthCheck.mask ridgeSupport832_001 = 0x1c01f800000000001b0619d000007e00f80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_001_checked :
    (ridgeSupport832_001.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_002_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_002 =
      (ridgeSupport832_002, ridgeSupport832_rest_003) := by decide +kernel
theorem ridgeSupport832_002_mask : RawNatGrowthCheck.mask ridgeSupport832_002 = 0x1f0000000000360c33a00000fc01f8000000000000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_002_checked :
    (ridgeSupport832_002.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_003_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_003 =
      (ridgeSupport832_003, ridgeSupport832_rest_004) := by decide +kernel
theorem ridgeSupport832_003_mask : RawNatGrowthCheck.mask ridgeSupport832_003 = 0x20000000000000003f007e00000000000000000000000000006c1867400001f8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_003_checked :
    (ridgeSupport832_003.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_004_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_004 =
      (ridgeSupport832_004, ridgeSupport832_rest_005) := by decide +kernel
theorem ridgeSupport832_004_mask : RawNatGrowthCheck.mask ridgeSupport832_004 = 0xe00fc0000000000d830ce800003f007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_004_checked :
    (ridgeSupport832_004.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_005_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_005 =
      (ridgeSupport832_005, ridgeSupport832_rest_006) := by decide +kernel
theorem ridgeSupport832_005_mask : RawNatGrowthCheck.mask ridgeSupport832_005 = 0x1f0360c33bb0619d00000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_005_checked :
    (ridgeSupport832_005.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_006_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_006 =
      (ridgeSupport832_006, ridgeSupport832_rest_007) := by decide +kernel
theorem ridgeSupport832_006_mask : RawNatGrowthCheck.mask ridgeSupport832_006 = 0x100000003f00000003f000fc000000003f00000003f0000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_006_checked :
    (ridgeSupport832_006.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_007_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_007 =
      (ridgeSupport832_007, ridgeSupport832_rest_008) := by decide +kernel
theorem ridgeSupport832_007_mask : RawNatGrowthCheck.mask ridgeSupport832_007 = 0x2c0fc000000000000003f00000000000003f00000003f00000000000003e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_007_checked :
    (ridgeSupport832_007.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
