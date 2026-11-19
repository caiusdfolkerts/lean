module

public import RootedFamilyClosure
public import RootedRawForest0022
public import RootedRawForest0022Dispositions
public import IdentityGrowthRenaming

@[expose] public section

/-! Exact finite classification for rooted case 22.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0022

open RootedForests.RootedRawForest0022
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed022.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed022.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed022.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed022.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed022.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed022.cells quota (0 : Fin 556) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed022.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed022.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed022.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed022.ridgeList c))
          FacetUniverses.RootedSevenMixed022.literalCompatible FacetUniverses.RootedSevenMixed022.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0022
