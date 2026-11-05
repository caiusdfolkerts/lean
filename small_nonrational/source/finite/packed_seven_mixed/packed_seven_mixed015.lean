module
prelude
public import PackedSevenMixed015Cache
public import PackedSevenMixed015Leaves
public import IdentityGrowthRenaming
public import PackedSevenMixed015Proof000
public import PackedSevenMixed015Proof001
public import PackedSevenMixed015Proof002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed015
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
theorem nodeTest_complete : Interval nodeTest 0 1575 := (interval_append nodeTest 0 640 1575 checkedInterval0 (interval_append nodeTest 640 1280 1575 checkedInterval640 checkedInterval1280))
def renamings (_ : Fin 1) := Renaming.identity
  (fun c : Fin 521 => has (ridgeList c)) literalCompatible kind
def root : Fin 1575 := ⟨1574, by decide⟩
def nodes : Fin 1575 → BatchedOrbitGrowth.Node 521 1024 1 18 1575 := decodedNodes rawNodes
theorem boundary_classification (B : List (Fin 521))
    (hB : Target (fun c => has (ridgeList c)) literalCompatible kind quota B)
    (hroot : (0 : Fin 521) ∈ B) : ∃ j, Same (family (leaves j)) (family B) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  obtain ⟨j, word, hsub, hne⟩ := complete_of_raw_checks candidateMasks badMasks rawKind
    (fun _ c => c) rawLeaves rawNodes cache quota renamings
    (fun _ => rfl) (fun _ => rfl) raw_kind_exact (fun _ _ => rfl)
    (fun j => (Bool.and_eq_true_iff.mp
      (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1)
    (fun i => (Bool.and_eq_true_iff.mp
      (nodeTest_complete i.val (Nat.zero_le _) i.isLt)).1)
    (fun i => (Bool.and_eq_true_iff.mp
      (nodeTest_complete i.val (Nat.zero_le _) i.isLt)).2)
    B hB root
    (by
      intro c hc
      change has (nodes root).cells c = true at hc
      rw [hrootCells] at hc
      have heq : c = 0 := List.eq_of_mem_singleton ((has_true [0] c).mp hc)
      subst c
      exact (has_true B 0).mpr hroot)
    (by
      refine ⟨0, ?_⟩
      change has (nodes root).cells 0 = true
      rw [hrootCells]
      rfl)
  have hw : OrbitGrowthDAG.applyWord renamings word B = B :=
    applyWord_identity (fun c => has (ridgeList c)) literalCompatible kind word B
  rw [hw] at hsub
  refine ⟨j, closed_leaf_eq_target ridgeList B (leaves j) hsub hne hB.no_three hB.connected ?_⟩
  exact (Bool.and_eq_true_iff.mp (leafTest_complete j.val (Nat.zero_le _) j.isLt)).2
#print axioms boundary_classification

end Papers.RationalityTen.PackedReplay.PackedSevenMixed015
