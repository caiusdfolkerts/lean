module

public import RawOutsidePlacement
public import OutsideBoundarySymmetry
public import RootedFacetCoverage

@[expose] public section

/-!
# Exact outside generators for a common-face block

The finite check inspects only the ten vertex labels of each adjacent
swap. The candidate-cell action is supplied by an independently checked
boundary frame, so this bridge does not assume that a literal permutation
preserves the candidate universe.
-/

noncomputable section
namespace Papers.RationalityTen.OutsidePlacementSemantics

open BoundaryGeneratorFrames OutsideBoundarySymmetry
open FacePlacementCodes RootedFacetCoverage LiteralMaskGeometry

theorem swapValue_eq_swap (a b v : Fin 10) :
    RawOutsidePlacement.swapValue a.val b.val v.val = (Equiv.swap a b v).val := by
  by_cases ha : v = a
  · subst v
    simp only [RawOutsidePlacement.swapValue, Equiv.swap_apply_def, ite_true]
  · have hva : v.val ≠ a.val := fun h => ha (Fin.ext h)
    by_cases hb : v = b
    · subst v
      simp only [RawOutsidePlacement.swapValue, Equiv.swap_apply_def, ha, hva,
        ite_false, ite_true]
    · have hvb : v.val ≠ b.val := fun h => hb (Fin.ext h)
      simp only [RawOutsidePlacement.swapValue, Equiv.swap_apply_def, ha, hb, hva,
        hvb, ite_false]

theorem outside_avoids_root {m g : Nat} [NeZero g]
    (vertexCode : Fin g → Nat) (root : ConcreteGrowth.Cell)
    (B : Block m) (raw : RawFacePlacement.Block) (H : Representation B raw)
    (hcheck : RawOutsidePlacement.blockCheck vertexCode root.vertices raw = true)
    (j : Fin B.outside) :
    outsideEmbedding B j ∉ (decodeCell root).vertices := by
  have hbit := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hcheck).1 j.val
    (List.mem_range.mpr (by simpa only [H.outside] using j.isLt))
  have htarget : RawFacePlacement.digit raw.targetForward (raw.shared + j.val) =
      (outsideEmbedding B j).val := by
    rw [H.shared]
    exact H.target_forward ⟨B.shared + j.val,
      lt_of_lt_of_le (Nat.add_lt_add_left j.isLt B.shared) B.target_le⟩
  rw [htarget] at hbit
  intro hv
  change outsideEmbedding B j ∈ maskSet root.vertices at hv
  rw [mem_maskSet] at hv
  rw [hv] at hbit
  exact Bool.false_ne_true hbit

theorem adjacent_frame {m n g : Nat} [NeZero g]
    (cells : Fin n → ConcreteGrowth.Cell) (generators : Fin g → BoundaryFrame cells)
    (vertexCode : Fin g → Nat)
    (hvertices : ∀ generator v,
      (generators generator).vertices v = TenGraphEdges.vertexMap (vertexCode generator) v)
    (root : ConcreteGrowth.Cell) (B : Block m) (raw : RawFacePlacement.Block)
    (H : Representation B raw)
    (hcheck : RawOutsidePlacement.blockCheck vertexCode root.vertices raw = true)
    (j : Fin (B.outside - 1)) :
    ∃ F : BoundaryFrame cells,
      F.vertices = (adjacentSwap B.outside j).viaEmbedding (outsideEmbedding B) := by
  refine ⟨generators (Fin.ofNat g j.val), ?_⟩
  rw [adjacentSwap_eq, viaEmbedding_swap]
  apply Equiv.ext
  intro v
  rw [hvertices]
  apply Fin.ext
  have hrow := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hcheck).2 j.val
    (List.mem_range.mpr (by simpa only [H.outside] using j.isLt))
  have hv := of_decide_eq_true (List.all_eq_true.mp hrow v (List.mem_finRange v))
  have hfirst : RawFacePlacement.digit raw.targetForward (raw.shared + j.val) =
      (outsideEmbedding B (adjacentFirst B.outside j)).val := by
    rw [H.shared]
    exact H.target_forward ⟨B.shared + (adjacentFirst B.outside j).val,
      lt_of_lt_of_le (Nat.add_lt_add_left (adjacentFirst B.outside j).isLt B.shared)
        B.target_le⟩
  have hsecond : RawFacePlacement.digit raw.targetForward (raw.shared + (j.val + 1)) =
      (outsideEmbedding B (adjacentSecond B.outside j)).val := by
    rw [H.shared]
    exact H.target_forward ⟨B.shared + (adjacentSecond B.outside j).val,
      lt_of_lt_of_le (Nat.add_lt_add_left (adjacentSecond B.outside j).isLt B.shared)
        B.target_le⟩
  rw [hfirst, hsecond] at hv
  exact hv.trans (swapValue_eq_swap _ _ _)

end Papers.RationalityTen.OutsidePlacementSemantics
