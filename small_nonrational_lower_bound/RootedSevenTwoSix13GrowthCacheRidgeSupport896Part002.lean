module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheRidgeSupport896Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport896_016_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_016 =
      (ridgeSupport896_016, ridgeSupport896_rest_017) := by decide +kernel
theorem ridgeSupport896_016_mask : RawNatGrowthCheck.mask ridgeSupport896_016 = (certNat% 0) := by decide +kernel
theorem ridgeSupport896_016_checked :
    (ridgeSupport896_016.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_017_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_017 =
      (ridgeSupport896_017, ridgeSupport896_rest_018) := by decide +kernel
theorem ridgeSupport896_017_mask : RawNatGrowthCheck.mask ridgeSupport896_017 = (certNat% 1) := by decide +kernel
theorem ridgeSupport896_017_checked :
    (ridgeSupport896_017.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_018_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_018 =
      (ridgeSupport896_018, ridgeSupport896_rest_019) := by decide +kernel
theorem ridgeSupport896_018_mask : RawNatGrowthCheck.mask ridgeSupport896_018 = (certNat% 2) := by decide +kernel
theorem ridgeSupport896_018_checked :
    (ridgeSupport896_018.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_019_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_019 =
      (ridgeSupport896_019, ridgeSupport896_rest_020) := by decide +kernel
theorem ridgeSupport896_019_mask : RawNatGrowthCheck.mask ridgeSupport896_019 = (certNat% 3) := by decide +kernel
theorem ridgeSupport896_019_checked :
    (ridgeSupport896_019.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_020_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_020 =
      (ridgeSupport896_020, ridgeSupport896_rest_021) := by decide +kernel
theorem ridgeSupport896_020_mask : RawNatGrowthCheck.mask ridgeSupport896_020 = (certNat% 4) := by decide +kernel
theorem ridgeSupport896_020_checked :
    (ridgeSupport896_020.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_021_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_021 =
      (ridgeSupport896_021, ridgeSupport896_rest_022) := by decide +kernel
theorem ridgeSupport896_021_mask : RawNatGrowthCheck.mask ridgeSupport896_021 = (certNat% 5) := by decide +kernel
theorem ridgeSupport896_021_checked :
    (ridgeSupport896_021.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_022_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_022 =
      (ridgeSupport896_022, ridgeSupport896_rest_023) := by decide +kernel
theorem ridgeSupport896_022_mask : RawNatGrowthCheck.mask ridgeSupport896_022 = (certNat% 6) := by decide +kernel
theorem ridgeSupport896_022_checked :
    (ridgeSupport896_022.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel
theorem ridgeSupport896_023_decode :
    PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_023 =
      (ridgeSupport896_023, ridgeSupport896_rest_024) := by decide +kernel
theorem ridgeSupport896_023_mask : RawNatGrowthCheck.mask ridgeSupport896_023 = (certNat% 7) := by decide +kernel
theorem ridgeSupport896_023_checked :
    (ridgeSupport896_023.all (fun c => hasNat (rawCells c).ridgeMasks 896)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
