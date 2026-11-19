module

public import Continuation.CycleBounds.K4BranchModels
public import Mathlib.Data.List.Chain

@[expose] public section

/-! # Extracting a bridge between successive cycle intersections -/

noncomputable section
namespace Unimodular.CycleBounds
attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-- If a walk changes the color of its visited marked vertices, two successive
marked intersections already change color. The intervening walk avoids the
marked set entirely. This is the path-segment extraction used in Proposition6.8. -/
theorem exists_bridge_segment {β : Type*} (S : Set V) (color : V → β)
    (l : List V) (a : V) (middle : List V)
    (ha : a ∈ S) (hm : ∀ x ∈ middle, x ∉ S)
    (hfuture : ∃ b ∈ l, b ∈ S ∧ color a ≠ color b) :
    ∃ pre x interior y post,
      a :: (middle ++ l) = pre ++ (x :: (interior ++ y :: post)) ∧
      x ∈ S ∧ y ∈ S ∧ color x ≠ color y ∧ ∀ z ∈ interior, z ∉ S := by
  induction l generalizing a middle with
  | nil =>
    obtain ⟨b, hb, _⟩ := hfuture
    cases hb
  | cons z l ih =>
    by_cases hz : z ∈ S
    · by_cases hac : color a = color z
      · have hfuture' : ∃ b ∈ l, b ∈ S ∧ color z ≠ color b := by
          obtain ⟨b, hb, hbS, hab⟩ := hfuture
          rcases List.mem_cons.mp hb with rfl | hb
          · exact (hab hac).elim
          · exact ⟨b, hb, hbS, fun h ↦ hab (hac.trans h)⟩
        obtain ⟨pre, x, inside, y, post, heq, hx, hy, hxy, hins⟩ :=
          ih z [] hz (by simp) hfuture'
        refine ⟨a :: (middle ++ pre), x, inside, y, post, ?_, hx, hy, hxy, hins⟩
        simpa only [List.nil_append, List.cons_append, List.append_assoc] using
          congrArg (fun w ↦ a :: (middle ++ w)) heq
      · exact ⟨[], a, middle, z, l, rfl, ha, hz, hac, hm⟩
    · have hfuture' : ∃ b ∈ l, b ∈ S ∧ color a ≠ color b := by
        obtain ⟨b, hb, hbS, hab⟩ := hfuture
        rcases List.mem_cons.mp hb with rfl | hb
        · exact (hz hbS).elim
        · exact ⟨b, hb, hbS, hab⟩
      have hm' : ∀ x ∈ middle ++ [z], x ∉ S := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hm x hx
        · rcases List.mem_singleton.mp hx with rfl
          exact hz
      simpa only [List.append_assoc, List.singleton_append] using
        ih a (middle ++ [z]) ha hm' hfuture'

/-- A bridge extracted from a graph walk remains an actual graph walk. -/
theorem bridge_isChain {R : V → V → Prop} {w pre inside post : List V} {x y : V}
    (hw : w.IsChain R) (heq : w = pre ++ (x :: (inside ++ y :: post))) :
    (x :: (inside ++ [y])).IsChain R := by
  apply hw.infix
  refine ⟨pre, post, ?_⟩
  simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using heq.symm

end Unimodular.CycleBounds
