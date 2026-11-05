module
prelude
public import RootedSixExtra06GrowthCacheRidgeSupport832Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport832_000_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_000 =
      (ridgeSupport832_000, ridgeSupport832_rest_001) := by decide +kernel
theorem ridgeSupport832_000_mask : RawNatGrowthCheck.mask ridgeSupport832_000 = 0x10000000000000001f803f0000000000000000000000000000000001f803f0000000000000000000000000000288020080000002000020000000 := by decide +kernel
theorem ridgeSupport832_000_checked :
    (ridgeSupport832_000.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_001_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_001 =
      (ridgeSupport832_001, ridgeSupport832_rest_002) := by decide +kernel
theorem ridgeSupport832_001_mask : RawNatGrowthCheck.mask ridgeSupport832_001 = 0x7007e00000000000000000000000000006c1867400001f803e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_001_checked :
    (ridgeSupport832_001.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_002_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_002 =
      (ridgeSupport832_002, ridgeSupport832_rest_003) := by decide +kernel
theorem ridgeSupport832_002_mask : RawNatGrowthCheck.mask ridgeSupport832_002 = 0x7c0000000000000000000000000000d830ce800003f007e0000000000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_002_checked :
    (ridgeSupport832_002.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_003_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_003 =
      (ridgeSupport832_003, ridgeSupport832_rest_004) := by decide +kernel
theorem ridgeSupport832_003_mask : RawNatGrowthCheck.mask ridgeSupport832_003 = 0x1000007e00fc0000000000000007e00fc0000000000000000000000000000000007e00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_003_checked :
    (ridgeSupport832_003.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_004_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_004 =
      (ridgeSupport832_004, ridgeSupport832_rest_005) := by decide +kernel
theorem ridgeSupport832_004_mask : RawNatGrowthCheck.mask ridgeSupport832_004 = 0x20c33a00000fc01f80000000001b0619c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_004_checked :
    (ridgeSupport832_004.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_005_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_005 =
      (ridgeSupport832_005, ridgeSupport832_rest_006) := by decide +kernel
theorem ridgeSupport832_005_mask : RawNatGrowthCheck.mask ridgeSupport832_005 = 0x4eec1867400001f803f00000000003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_005_checked :
    (ridgeSupport832_005.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_006_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_006 =
      (ridgeSupport832_006, ridgeSupport832_rest_007) := by decide +kernel
theorem ridgeSupport832_006_mask : RawNatGrowthCheck.mask ridgeSupport832_006 = 0x100000079e02b00000079e02bd830800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_006_checked :
    (ridgeSupport832_006.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_007_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport832_rest_007 =
      (ridgeSupport832_007, ridgeSupport832_rest_008) := by decide +kernel
theorem ridgeSupport832_007_mask : RawNatGrowthCheck.mask ridgeSupport832_007 = 0x9e02b00000079e02b00000000000000000000000079e02a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_007_checked :
    (ridgeSupport832_007.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
