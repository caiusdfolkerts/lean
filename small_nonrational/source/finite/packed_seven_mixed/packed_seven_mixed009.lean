module
prelude
public import PackedSevenMixed009Cache
public import PackedSevenMixed009Leaves
public import IdentityGrowthRenaming
public import PackedSevenMixed009Proof000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed009
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
theorem nodeTest_complete : Interval nodeTest 0 508 := checkedInterval0
def renamings (_ : Fin 1) := Renaming.identity
  (fun c : Fin 910 => has (ridgeList c)) literalCompatible kind
def root : Fin 508 := ⟨507, by decide⟩
def nodes : Fin 508 → BatchedOrbitGrowth.Node 910 1024 1 1 508 := decodedNodes rawNodes
theorem boundary_classification (B : List (Fin 910))
    (hB : Target (fun c => has (ridgeList c)) literalCompatible kind quota B)
    (hroot : (0 : Fin 910) ∈ B) : ∃ j, Same (family (leaves j)) (family B) := by
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

end Papers.RationalityTen.PackedReplay.PackedSevenMixed009
