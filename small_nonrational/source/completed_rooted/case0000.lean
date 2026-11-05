module

public import RootedFamilyClosure
public import PackedSevenMixed000Classification
public import PackedSevenMixed000Dispositions
public import RootedSevenMixed000WellFormed

@[expose] public section

/-! Exact finite classification for rooted case 0.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0000

open PackedReplay.PackedSevenMixed000
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed000.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed000.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed000.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed000.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed000.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed000.cells quota (0 : Fin 646) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed000.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed000.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed000.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0000
