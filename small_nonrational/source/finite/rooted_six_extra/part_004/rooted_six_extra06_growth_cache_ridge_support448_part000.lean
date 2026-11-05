module
prelude
public import RootedSixExtra06GrowthCacheRidgeSupport448Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport448_000_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport448_rest_000 =
      (ridgeSupport448_000, ridgeSupport448_rest_001) := by decide +kernel
theorem ridgeSupport448_000_mask : RawNatGrowthCheck.mask ridgeSupport448_000 = 0x40000000000000007e00fc0000000000000000000000000000000007e00fc00000000000000000222008020000000800008000000 := by decide +kernel
theorem ridgeSupport448_000_checked :
    (ridgeSupport448_000.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_001_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport448_rest_001 =
      (ridgeSupport448_001, ridgeSupport448_rest_002) := by decide +kernel
theorem ridgeSupport448_001_mask : RawNatGrowthCheck.mask ridgeSupport448_001 = 0x1c01f8000000000000000000b68d1c0000000000000007e00f800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_001_checked :
    (ridgeSupport448_001.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_002_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport448_rest_002 =
      (ridgeSupport448_002, ridgeSupport448_rest_003) := by decide +kernel
theorem ridgeSupport448_002_mask : RawNatGrowthCheck.mask ridgeSupport448_002 = 0x1f00000000000000000016d1a38000000000000000fc01f8000000000000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_002_checked :
    (ridgeSupport448_002.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_003_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport448_rest_003 =
      (ridgeSupport448_003, ridgeSupport448_rest_004) := by decide +kernel
theorem ridgeSupport448_003_mask : RawNatGrowthCheck.mask ridgeSupport448_003 = 0x10000000000000001f803f0000000000000001f803f0000000000000000000000000000000001f8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_003_checked :
    (ridgeSupport448_003.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_004_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport448_rest_004 =
      (ridgeSupport448_004, ridgeSupport448_rest_005) := by decide +kernel
theorem ridgeSupport448_004_mask : RawNatGrowthCheck.mask ridgeSupport448_004 = 0x3468e0000000000000003f007e2da346000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_004_checked :
    (ridgeSupport448_004.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_005_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport448_rest_005 =
      (ridgeSupport448_005, ridgeSupport448_rest_006) := by decide +kernel
theorem ridgeSupport448_005_mask : RawNatGrowthCheck.mask ridgeSupport448_005 = 0xa38b68d1c0000000000000007e00fc580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_005_checked :
    (ridgeSupport448_005.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_006_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport448_rest_006 =
      (ridgeSupport448_006, ridgeSupport448_rest_007) := by decide +kernel
theorem ridgeSupport448_006_mask : RawNatGrowthCheck.mask ridgeSupport448_006 = 0x1000000035d75000000035d7516d1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_006_checked :
    (ridgeSupport448_006.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel
theorem ridgeSupport448_007_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport448_rest_007 =
      (ridgeSupport448_007, ridgeSupport448_rest_008) := by decide +kernel
theorem ridgeSupport448_007_mask : RawNatGrowthCheck.mask ridgeSupport448_007 = 0x1d75000000035d75000000000000000000000000035d740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport448_007_checked :
    (ridgeSupport448_007.all (fun c => hasNat (rawCells c).ridgeMasks 448)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
