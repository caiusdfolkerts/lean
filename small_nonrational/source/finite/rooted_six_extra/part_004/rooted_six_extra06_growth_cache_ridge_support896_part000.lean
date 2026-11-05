module
prelude
public import RootedSixExtra06GrowthCacheRidgeSupport896Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport896_000_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport896_rest_000 =
      (ridgeSupport896_000, ridgeSupport896_rest_001) := by decide +kernel
theorem ridgeSupport896_000_mask : RawNatGrowthCheck.mask ridgeSupport896_000 = 0x20000000000000003f007e0000000000000000000000000000000003f007e000000000000000000000000000000000310040100000004000040000000 := by decide +kernel
theorem ridgeSupport896_000_checked :
    (ridgeSupport896_000.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_001_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport896_rest_001 =
      (ridgeSupport896_001, ridgeSupport896_rest_002) := by decide +kernel
theorem ridgeSupport896_001_mask : RawNatGrowthCheck.mask ridgeSupport896_001 = 0xe00fc00000000000000000000000000000000036c01fbf007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport896_001_checked :
    (ridgeSupport896_001.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_002_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport896_rest_002 =
      (ridgeSupport896_002, ridgeSupport896_rest_003) := by decide +kernel
theorem ridgeSupport896_002_mask : RawNatGrowthCheck.mask ridgeSupport896_002 = 0xf80000000000000000000000000000000006d803f7e00fc000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport896_002_checked :
    (ridgeSupport896_002.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_003_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport896_rest_003 =
      (ridgeSupport896_003, ridgeSupport896_rest_004) := by decide +kernel
theorem ridgeSupport896_003_mask : RawNatGrowthCheck.mask ridgeSupport896_003 = 0x2fc01f8000000000000000fc01f8000000000000000000000000000000000fc0100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport896_003_checked :
    (ridgeSupport896_003.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_004_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport896_rest_004 =
      (ridgeSupport896_004, ridgeSupport896_rest_005) := by decide +kernel
theorem ridgeSupport896_004_mask : RawNatGrowthCheck.mask ridgeSupport896_004 = 0x1600fdf803f0000000000000000db007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport896_004_checked :
    (ridgeSupport896_004.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_005_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport896_rest_005 =
      (ridgeSupport896_005, ridgeSupport896_rest_006) := by decide +kernel
theorem ridgeSupport896_005_mask : RawNatGrowthCheck.mask ridgeSupport896_005 = 0x1f36c01fbf007e0000000000000001a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport896_005_checked :
    (ridgeSupport896_005.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_006_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport896_rest_006 =
      (ridgeSupport896_006, ridgeSupport896_rest_007) := by decide +kernel
theorem ridgeSupport896_006_mask : RawNatGrowthCheck.mask ridgeSupport896_006 = 0x40000000aebac0000000aebac06d80200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport896_006_checked :
    (ridgeSupport896_006.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_007_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport896_rest_007 =
      (ridgeSupport896_007, ridgeSupport896_rest_008) := by decide +kernel
theorem ridgeSupport896_007_mask : RawNatGrowthCheck.mask ridgeSupport896_007 = 0x6bac0000000aebac0000000000000000000000000aeba800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport896_007_checked :
    (ridgeSupport896_007.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
