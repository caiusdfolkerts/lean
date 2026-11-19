module

public import RootedFamilyClosure
public import RootedSmallBoundaryFrames
public import Consolidated.SmallFacetEncoding
public import SmallRawForest02
public import SmallRawForest02Dispositions
public import SmallSubsumedForest03
public import SmallSubsumedForest03Dispositions
public import SmallSubsumedForest04
public import SmallSubsumedForest04Dispositions
public import SmallSubsumedForest05
public import SmallSubsumedForest05Dispositions
public import SmallSubsumedForest06
public import SmallSubsumedForest06Dispositions
public import SmallSubsumedForest07
public import SmallSubsumedForest07Dispositions
public import SmallSubsumedForest08
public import SmallSubsumedForest08Dispositions
public import SmallSubsumedForest09
public import SmallSubsumedForest09Dispositions
public import SmallSubsumedForest10
public import SmallSubsumedForest10Dispositions
public import SmallSubsumedForest11
public import SmallSubsumedForest11Dispositions
public import SmallSubsumedForest12
public import SmallSubsumedForest12Dispositions
public import SmallSubsumedForest13
public import SmallSubsumedForest13Dispositions
public import SmallSubsumedForest14
public import SmallSubsumedForest14Dispositions
public import SmallSubsumedForest15
public import SmallSubsumedForest15Dispositions
public import SmallSubsumedForest17
public import SmallSubsumedForest17Dispositions
public import SmallSubsumedForest18
public import SmallSubsumedForest18Dispositions
public import SmallSubsumedForest20
public import SmallSubsumedForest20Dispositions
public import SmallSubsumedForest21
public import SmallSubsumedForest21Dispositions
public import SmallSubsumedForest22
public import SmallSubsumedForest22Dispositions

@[expose] public section

/-! Complete finite certificates for all nineteen rooted small-facet rows.
Each certificate retains its precise facet quota and every terminal boundary.
The equality with the geometric quota is proved explicitly for every row. -/

noncomputable section

namespace Papers.RationalityTen.CompletedSmall.Row02

open SmallRawForests.SmallRawForest02
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 11 10 0 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 11 10 0)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row02

namespace Papers.RationalityTen.CompletedSmall.Row03

open SmallRawForests.SmallSubsumedForest03
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 11 10 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 11 10 1)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row03

namespace Papers.RationalityTen.CompletedSmall.Row04

open SmallRawForests.SmallSubsumedForest04
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 11 11 0 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 11 11 0)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row04

namespace Papers.RationalityTen.CompletedSmall.Row05

open SmallRawForests.SmallSubsumedForest05
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 11 11 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 11 11 1)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row05

namespace Papers.RationalityTen.CompletedSmall.Row06

open SmallRawForests.SmallSubsumedForest06
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 11 11 2 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 11 11 2)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row06

namespace Papers.RationalityTen.CompletedSmall.Row07

open SmallRawForests.SmallSubsumedForest07
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 12 10 0 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 12 10 0)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row07

namespace Papers.RationalityTen.CompletedSmall.Row08

open SmallRawForests.SmallSubsumedForest08
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 12 10 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 12 10 1)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row08

namespace Papers.RationalityTen.CompletedSmall.Row09

open SmallRawForests.SmallSubsumedForest09
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 12 11 0 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 12 11 0)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row09

namespace Papers.RationalityTen.CompletedSmall.Row10

open SmallRawForests.SmallSubsumedForest10
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 12 11 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 12 11 1)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row10

namespace Papers.RationalityTen.CompletedSmall.Row11

open SmallRawForests.SmallSubsumedForest11
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 12 11 2 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 12 11 2)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row11

namespace Papers.RationalityTen.CompletedSmall.Row12

open SmallRawForests.SmallSubsumedForest12
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 12 12 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 12 12 1)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row12

namespace Papers.RationalityTen.CompletedSmall.Row13

open SmallRawForests.SmallSubsumedForest13
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 12 12 2 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 12 12 2)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row13

namespace Papers.RationalityTen.CompletedSmall.Row14

open SmallRawForests.SmallSubsumedForest14
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 12 12 3 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 12 12 3)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row14

namespace Papers.RationalityTen.CompletedSmall.Row15

open SmallRawForests.SmallSubsumedForest15
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 13 10 0 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 13 10 0)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row15

namespace Papers.RationalityTen.CompletedSmall.Row17

open SmallRawForests.SmallSubsumedForest17
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 13 11 0 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 13 11 0)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row17

namespace Papers.RationalityTen.CompletedSmall.Row18

open SmallRawForests.SmallSubsumedForest18
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 13 11 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 13 11 1)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row18

namespace Papers.RationalityTen.CompletedSmall.Row20

open SmallRawForests.SmallSubsumedForest20
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 13 12 2 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 13 12 2)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row20

namespace Papers.RationalityTen.CompletedSmall.Row21

open SmallRawForests.SmallSubsumedForest21
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 13 12 3 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 13 12 3)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row21

namespace Papers.RationalityTen.CompletedSmall.Row22

open SmallRawForests.SmallSubsumedForest22
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin leafCount) :
    (leaves j).map FacetUniverses.Small.cells =
      (rawLeaves j.val).map RootedSmallCache.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.Small.cells =
        ((leaves j).map Fin.val).map RootedSmallCache.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedSmallCache.rawCells := by rw [hval]

def rawClassification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells quota FacetUniverses.Small.root where
  wellFormed := RootedSmallBoundaryFrames.cells_wellFormed
  generatorCount := 1440
  frames := RootedSmallBoundaryFrames.frame
  leafCount := leafCount
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedSmallCache.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (RootedSmallBoundaryFrames.frame f).toBoundaryRenaming
      RootedSmallBoundaryFrames.cells_wellFormed)
    RootedSmallBoundaryFrames.maps_exact B hB hroot

theorem quota_eq : quota = SmallFacetTargetBudgets.quota 13 13 4 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.Small.cells (SmallFacetTargetBudgets.quota 13 13 4)
    FacetUniverses.Small.root := by
  rw [← quota_eq]
  exact rawClassification

#print axioms classification
end Papers.RationalityTen.CompletedSmall.Row22
