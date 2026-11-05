module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport832Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport832_000_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport832_rest_000 =
      (ridgeSupport832_000, ridgeSupport832_rest_001) := by decide +kernel
theorem ridgeSupport832_000_mask : RawNatGrowthCheck.mask ridgeSupport832_000 = 0xce0000060780000050c3380000181e00000000000c0f0000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_000_checked :
    (ridgeSupport832_000.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_001_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport832_rest_001 =
      (ridgeSupport832_001, ridgeSupport832_rest_002) := by decide +kernel
theorem ridgeSupport832_001_mask : RawNatGrowthCheck.mask ridgeSupport832_001 = 0xbac00285e85c0000000000000000028619d430000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_001_checked :
    (ridgeSupport832_001.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_002_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport832_rest_002 =
      (ridgeSupport832_002, ridgeSupport832_rest_003) := by decide +kernel
theorem ridgeSupport832_002_mask : RawNatGrowthCheck.mask ridgeSupport832_002 = 0x4302bac00285e85c3ac30200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_002_checked :
    (ridgeSupport832_002.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_003_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport832_rest_003 =
      (ridgeSupport832_003, ridgeSupport832_rest_004) := by decide +kernel
theorem ridgeSupport832_003_mask : RawNatGrowthCheck.mask ridgeSupport832_003 = 0x1ac302bac00285e85c3a800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_003_checked :
    (ridgeSupport832_003.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_004_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport832_rest_004 =
      (ridgeSupport832_004, ridgeSupport832_rest_005) := by decide +kernel
theorem ridgeSupport832_004_mask : RawNatGrowthCheck.mask ridgeSupport832_004 = 0x1d4500f3c000000000ac3ac30005c00000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_004_checked :
    (ridgeSupport832_004.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_005_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport832_rest_005 =
      (ridgeSupport832_005, ridgeSupport832_rest_006) := by decide +kernel
theorem ridgeSupport832_005_mask : RawNatGrowthCheck.mask ridgeSupport832_005 = 0x430005d4500f3c000000000ac3ac30004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_005_checked :
    (ridgeSupport832_005.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_006_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport832_rest_006 =
      (ridgeSupport832_006, ridgeSupport832_rest_007) := by decide +kernel
theorem ridgeSupport832_006_mask : RawNatGrowthCheck.mask ridgeSupport832_006 = 0x15030000000000000000000000030c3014500f3c000000000ac3a800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_006_checked :
    (ridgeSupport832_006.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel
theorem ridgeSupport832_007_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport832_rest_007 =
      (ridgeSupport832_007, ridgeSupport832_rest_008) := by decide +kernel
theorem ridgeSupport832_007_mask : RawNatGrowthCheck.mask ridgeSupport832_007 = 0x10000000c30005035030030c00140d40c00c30005020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport832_007_checked :
    (ridgeSupport832_007.all (fun c => hasNat (rawCells c).ridgeMasks 832)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
