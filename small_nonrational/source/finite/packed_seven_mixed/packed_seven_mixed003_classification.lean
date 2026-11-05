module
prelude
public import PackedSevenMixed003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed003
open Papers.RationalityTen ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthRenaming

theorem leaves_nodup : ∀ j, (leaves j).Nodup := by decide +kernel

/-- Exact closed-leaf classification, retaining the no-duplicates certificate. -/
theorem boundary_classification_nodup (B : List (Fin 646))
    (hB : Target (fun c => has (ridgeList c)) literalCompatible kind quota B)
    (hroot : (0 : Fin 646) ∈ B) :
    ∃ j, (leaves j).Nodup ∧ Same (family (leaves j)) (family B) := by
  obtain ⟨j, hj⟩ := boundary_classification B hB hroot
  exact ⟨j, leaves_nodup j, hj⟩

/-- Uniform word-action interface; this family needs only the empty word. -/
theorem boundary_classification_word (B : List (Fin 646))
    (hB : Target (fun c => has (ridgeList c)) literalCompatible kind quota B)
    (hroot : (0 : Fin 646) ∈ B) :
    ∃ (j : Fin 1) (word : List (Fin 1)), (leaves j).Nodup ∧
      Same (family (leaves j)) (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  obtain ⟨j, hnodup, hj⟩ := boundary_classification_nodup B hB hroot
  exact ⟨j, [], hnodup, hj⟩
#print axioms boundary_classification_word
end Papers.RationalityTen.PackedReplay.PackedSevenMixed003
