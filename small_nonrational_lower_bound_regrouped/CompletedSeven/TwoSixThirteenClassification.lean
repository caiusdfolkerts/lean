module

public import BoundaryGeneratorFrames
public import RootedFamilyClosure
public import RootedSevenTwoSix13Generators
public import RootedSevenTwoSix13GrowthCache
public import CompletedSeven.Certificates
public import CompletedSeven.TwoSixThirteenCoverage
public import RootedSubsumedForest0470
public import RootedSubsumedForest0470Dispositions
public import RootedSubsumedForest0471
public import RootedSubsumedForest0471Dispositions
public import RootedSubsumedForest0472
public import RootedSubsumedForest0472Dispositions
public import RootedSubsumedForest0473
public import RootedSubsumedForest0473Dispositions
public import RootedSubsumedForest0474
public import RootedSubsumedForest0474Dispositions
public import RootedSubsumedForest0475
public import RootedSubsumedForest0475Dispositions
public import RootedSubsumedForest0476
public import RootedSubsumedForest0476Dispositions
public import RootedSubsumedForest0477
public import RootedSubsumedForest0477Dispositions

/-! Complete finite certificates for canonical seven-vertex template 13 and
each of the eight possible square-pyramid counts. The finite classification
bodies are retained; the certificate facades make their literal quota arithmetic
explicit. The independent geometric lemma proves that every residual polytope
with two six-vertex facets has this template. -/

/- Source module: CompletedRooted.RootedSevenTwoSix13Frames -/
@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSevenTwoSix13

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 4)
    (i : Fin 2038) :
    inverseCheckAt (FacetUniverses.RootedSevenTwoSix13.Generators.forward g)
      (FacetUniverses.RootedSevenTwoSix13.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenTwoSix13.Generators.vertexCode g))
      (FacetUniverses.RootedSevenTwoSix13.cells i)
      (FacetUniverses.RootedSevenTwoSix13.cells
        (FacetUniverses.RootedSevenTwoSix13.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenTwoSix13.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenTwoSix13.Generators.cell_checked g i

def generator (g : Fin 4) :
    BoundaryFrame FacetUniverses.RootedSevenTwoSix13.cells :=
  checkedFrame FacetUniverses.RootedSevenTwoSix13.cells
    (FacetUniverses.RootedSevenTwoSix13.Generators.vertexCode g)
    (FacetUniverses.RootedSevenTwoSix13.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSevenTwoSix13.Generators.vertex_checks g)
    (FacetUniverses.RootedSevenTwoSix13.Generators.forward g)
    (FacetUniverses.RootedSevenTwoSix13.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 36) :
    BoundaryFrame FacetUniverses.RootedSevenTwoSix13.cells :=
  wordFrame FacetUniverses.RootedSevenTwoSix13.cells generator
    (FacetUniverses.RootedSevenTwoSix13.Generators.words f)

theorem cells_wellFormed (i : Fin 2038) :
    WellFormed (FacetUniverses.RootedSevenTwoSix13.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSevenTwoSix13.well_formed i)

theorem maps_exact (f : Fin 36) (i : Fin 2038) :
    FacetUniverses.RootedSevenTwoSix13.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSevenTwoSix13.cells generator
    FacetUniverses.RootedSevenTwoSix13.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSevenTwoSix13.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSevenTwoSix13.Generators.words f)
    (FacetUniverses.RootedSevenTwoSix13.Generators.rawWords f.val)
    (FacetUniverses.RootedSevenTwoSix13.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSevenTwoSix13

end
end


/- Source module: CompletedRooted.Case0470 -/
@[expose] public section

/-! Exact finite classification for rooted case 470.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0470

open RootedForests.RootedSubsumedForest0470
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenTwoSix13.cells quota (0 : Fin 2038) where
  wellFormed := CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed
  generatorCount := 36
  frames := CompletedRootedFrames.RootedSevenTwoSix13.frame
  leafCount := 1
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (CompletedRootedFrames.RootedSevenTwoSix13.frame f).toBoundaryRenaming
      CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed)
    CompletedRootedFrames.RootedSevenTwoSix13.maps_exact B hB hroot

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0470

end
end


/- Source module: CompletedRooted.Case0471 -/
@[expose] public section

/-! Exact finite classification for rooted case 471.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0471

open RootedForests.RootedSubsumedForest0471
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenTwoSix13.cells quota (0 : Fin 2038) where
  wellFormed := CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed
  generatorCount := 36
  frames := CompletedRootedFrames.RootedSevenTwoSix13.frame
  leafCount := 1
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (CompletedRootedFrames.RootedSevenTwoSix13.frame f).toBoundaryRenaming
      CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed)
    CompletedRootedFrames.RootedSevenTwoSix13.maps_exact B hB hroot

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0471

end
end


/- Source module: CompletedRooted.Case0472 -/
@[expose] public section

/-! Exact finite classification for rooted case 472.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0472

open RootedForests.RootedSubsumedForest0472
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenTwoSix13.cells quota (0 : Fin 2038) where
  wellFormed := CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed
  generatorCount := 36
  frames := CompletedRootedFrames.RootedSevenTwoSix13.frame
  leafCount := 1
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (CompletedRootedFrames.RootedSevenTwoSix13.frame f).toBoundaryRenaming
      CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed)
    CompletedRootedFrames.RootedSevenTwoSix13.maps_exact B hB hroot

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0472

end
end


/- Source module: CompletedRooted.Case0473 -/
@[expose] public section

/-! Exact finite classification for rooted case 473.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0473

open RootedForests.RootedSubsumedForest0473
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenTwoSix13.cells quota (0 : Fin 2038) where
  wellFormed := CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed
  generatorCount := 36
  frames := CompletedRootedFrames.RootedSevenTwoSix13.frame
  leafCount := 1
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (CompletedRootedFrames.RootedSevenTwoSix13.frame f).toBoundaryRenaming
      CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed)
    CompletedRootedFrames.RootedSevenTwoSix13.maps_exact B hB hroot

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0473

end
end


/- Source module: CompletedRooted.Case0474 -/
@[expose] public section

/-! Exact finite classification for rooted case 474.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0474

open RootedForests.RootedSubsumedForest0474
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenTwoSix13.cells quota (0 : Fin 2038) where
  wellFormed := CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed
  generatorCount := 36
  frames := CompletedRootedFrames.RootedSevenTwoSix13.frame
  leafCount := 1
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (CompletedRootedFrames.RootedSevenTwoSix13.frame f).toBoundaryRenaming
      CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed)
    CompletedRootedFrames.RootedSevenTwoSix13.maps_exact B hB hroot

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0474

end
end


/- Source module: CompletedRooted.Case0475 -/
@[expose] public section

/-! Exact finite classification for rooted case 475.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0475

open RootedForests.RootedSubsumedForest0475
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenTwoSix13.cells quota (0 : Fin 2038) where
  wellFormed := CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed
  generatorCount := 36
  frames := CompletedRootedFrames.RootedSevenTwoSix13.frame
  leafCount := 1
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (CompletedRootedFrames.RootedSevenTwoSix13.frame f).toBoundaryRenaming
      CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed)
    CompletedRootedFrames.RootedSevenTwoSix13.maps_exact B hB hroot

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0475

end
end


/- Source module: CompletedRooted.Case0476 -/
@[expose] public section

/-! Exact finite classification for rooted case 476.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0476

open RootedForests.RootedSubsumedForest0476
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenTwoSix13.cells quota (0 : Fin 2038) where
  wellFormed := CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed
  generatorCount := 36
  frames := CompletedRootedFrames.RootedSevenTwoSix13.frame
  leafCount := 1
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (CompletedRootedFrames.RootedSevenTwoSix13.frame f).toBoundaryRenaming
      CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed)
    CompletedRootedFrames.RootedSevenTwoSix13.maps_exact B hB hroot

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0476

end
end


/- Source module: CompletedRooted.Case0477 -/
@[expose] public section

/-! Exact finite classification for rooted case 477.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0477

open RootedForests.RootedSubsumedForest0477
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenTwoSix13.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenTwoSix13.cells quota (0 : Fin 2038) where
  wellFormed := CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed
  generatorCount := 36
  frames := CompletedRootedFrames.RootedSevenTwoSix13.frame
  leafCount := 1
  leaves := leaves
  rawLeaves := fun j => (rawLeaves j.val).map RootedCaches.RootedSevenTwoSix13.rawCells
  raw_exact := raw_leaves_exact
  certificates := disposition
  checked := disposition_checked
  complete := fun B hB hroot => boundary_classification
    (fun f => (CompletedRootedFrames.RootedSevenTwoSix13.frame f).toBoundaryRenaming
      CompletedRootedFrames.RootedSevenTwoSix13.cells_wellFormed)
    CompletedRootedFrames.RootedSevenTwoSix13.maps_exact B hB hroot

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0477

end
end


@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0470
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedSubsumedForest0470.quota = rowQuota 0 7 0 2 := by
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

/-- Complete finite and geometric certificate for case 470. -/
def certificate : TwoSixCertificate 13 0 where
  cellCount := FacetUniverses.RootedSevenTwoSix13.cellCount
  cells := FacetUniverses.RootedSevenTwoSix13.cells
  root := 0
  classification := by
    change RootedFamilyClosure.FiniteClassification _ (rowQuota 0 7 0 2) _
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0470.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenTwoSix13.rowCoverage 0

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0470
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0471
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedSubsumedForest0471.quota = rowQuota 0 6 1 2 := by
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

/-- Complete finite and geometric certificate for case 471. -/
def certificate : TwoSixCertificate 13 1 where
  cellCount := FacetUniverses.RootedSevenTwoSix13.cellCount
  cells := FacetUniverses.RootedSevenTwoSix13.cells
  root := 0
  classification := by
    change RootedFamilyClosure.FiniteClassification _ (rowQuota 0 6 1 2) _
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0471.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenTwoSix13.rowCoverage 1

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0471
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0472
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedSubsumedForest0472.quota = rowQuota 0 5 2 2 := by
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

/-- Complete finite and geometric certificate for case 472. -/
def certificate : TwoSixCertificate 13 2 where
  cellCount := FacetUniverses.RootedSevenTwoSix13.cellCount
  cells := FacetUniverses.RootedSevenTwoSix13.cells
  root := 0
  classification := by
    change RootedFamilyClosure.FiniteClassification _ (rowQuota 0 5 2 2) _
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0472.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenTwoSix13.rowCoverage 2

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0472
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0473
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedSubsumedForest0473.quota = rowQuota 0 4 3 2 := by
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

/-- Complete finite and geometric certificate for case 473. -/
def certificate : TwoSixCertificate 13 3 where
  cellCount := FacetUniverses.RootedSevenTwoSix13.cellCount
  cells := FacetUniverses.RootedSevenTwoSix13.cells
  root := 0
  classification := by
    change RootedFamilyClosure.FiniteClassification _ (rowQuota 0 4 3 2) _
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0473.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenTwoSix13.rowCoverage 3

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0473
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0474
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedSubsumedForest0474.quota = rowQuota 0 3 4 2 := by
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

/-- Complete finite and geometric certificate for case 474. -/
def certificate : TwoSixCertificate 13 4 where
  cellCount := FacetUniverses.RootedSevenTwoSix13.cellCount
  cells := FacetUniverses.RootedSevenTwoSix13.cells
  root := 0
  classification := by
    change RootedFamilyClosure.FiniteClassification _ (rowQuota 0 3 4 2) _
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0474.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenTwoSix13.rowCoverage 4

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0474
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0475
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedSubsumedForest0475.quota = rowQuota 0 2 5 2 := by
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

/-- Complete finite and geometric certificate for case 475. -/
def certificate : TwoSixCertificate 13 5 where
  cellCount := FacetUniverses.RootedSevenTwoSix13.cellCount
  cells := FacetUniverses.RootedSevenTwoSix13.cells
  root := 0
  classification := by
    change RootedFamilyClosure.FiniteClassification _ (rowQuota 0 2 5 2) _
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0475.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenTwoSix13.rowCoverage 5

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0475
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0476
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedSubsumedForest0476.quota = rowQuota 0 1 6 2 := by
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

/-- Complete finite and geometric certificate for case 476. -/
def certificate : TwoSixCertificate 13 6 where
  cellCount := FacetUniverses.RootedSevenTwoSix13.cellCount
  cells := FacetUniverses.RootedSevenTwoSix13.cells
  root := 0
  classification := by
    change RootedFamilyClosure.FiniteClassification _ (rowQuota 0 1 6 2) _
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0476.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenTwoSix13.rowCoverage 6

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0476
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0477
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedSubsumedForest0477.quota = rowQuota 0 0 7 2 := by
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

/-- Complete finite and geometric certificate for case 477. -/
def certificate : TwoSixCertificate 13 7 where
  cellCount := FacetUniverses.RootedSevenTwoSix13.cellCount
  cells := FacetUniverses.RootedSevenTwoSix13.cells
  root := 0
  classification := by
    change RootedFamilyClosure.FiniteClassification _ (rowQuota 0 0 7 2) _
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0477.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenTwoSix13.rowCoverage 7

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0477
end
end
