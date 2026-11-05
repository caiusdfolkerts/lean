module

public import Continuation.CycleBounds.K4Subdivision
public import Mathlib.Data.List.Permutation

@[expose] public section

/-! # Cyclic graph words and ordered subword decompositions -/

noncomputable section
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E : Type*}

/-- A simple graph cycle listed once. The doubled word expresses all ordinary
adjacencies, including the closing edge, without choosing a privileged start. -/
structure CycleWord (G : IncidenceGraph V E) (w : List V) : Prop where
  nonempty : w ≠ []
  nodup : w.Nodup
  chain : (w ++ w).IsChain (Adj G)

theorem CycleWord.rotate {G : IncidenceGraph V E} {u v : List V}
    (h : CycleWord G (u ++ v)) : CycleWord G (v ++ u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hh
    obtain ⟨hv, hu⟩ := List.append_eq_nil_iff.mp hh
    exact h.nonempty (List.append_eq_nil_iff.mpr ⟨hu, hv⟩)
  · exact (List.perm_append_comm : List.Perm (u ++ v) (v ++ u)).nodup_iff.mp h.nodup
  · have hthree := h.chain.append_overlap h.chain h.nonempty
    apply hthree.infix
    refine ⟨u, v, ?_⟩
    simp only [List.append_assoc]

theorem CycleWord.rotate_of_eq {G : IncidenceGraph V E} {w u v : List V}
    (h : CycleWord G w) (heq : w = u ++ v) : CycleWord G (v ++ u) := by
  subst w
  exact h.rotate

/-- Every displayed non-wrapping arc is an actual graph walk. -/
theorem CycleWord.arc {G : IncidenceGraph V E} {w pre inside post : List V} {a b : V}
    (h : CycleWord G w) (heq : w = pre ++ (a :: (inside ++ b :: post))) :
    (a :: (inside ++ [b])).IsChain (Adj G) :=
  bridge_isChain h.chain.left_of_append heq

/-- Split a sublist at its first selected element while preserving the order
 of all remaining selected elements. -/
theorem sublist_cons_split {a : V} {l w : List V} (h : (a :: l).Sublist w) :
    ∃ pre post, w = pre ++ a :: post ∧ l.Sublist post := by
  induction w with
  | nil => cases h
  | cons x w ih =>
    rcases List.sublist_cons_iff.mp h with htail | ⟨r, heq, hr⟩
    · obtain ⟨pre, post, hw, hp⟩ := ih htail
      exact ⟨x :: pre, post, by simp only [hw, List.cons_append], hp⟩
    · obtain ⟨hax, hlr⟩ := List.cons.inj heq
      subst x
      subst r
      exact ⟨[], w, rfl, hr⟩

theorem sublist_four_split {a b c d : V} {w : List V}
    (h : [a, b, c, d].Sublist w) :
    ∃ p₀ p₁ p₂ p₃ p₄ : List V,
      w = p₀ ++ a :: (p₁ ++ b :: (p₂ ++ c :: (p₃ ++ d :: p₄))) := by
  obtain ⟨p₀, w₁, h₀, h₁⟩ := sublist_cons_split h
  obtain ⟨p₁, w₂, h₁', h₂⟩ := sublist_cons_split h₁
  obtain ⟨p₂, w₃, h₂', h₃⟩ := sublist_cons_split h₂
  obtain ⟨p₃, p₄, h₃', _⟩ := sublist_cons_split h₃
  exact ⟨p₀, p₁, p₂, p₃, p₄, by simp only [h₀, h₁', h₂', h₃']⟩

/-- An alternating four-label subword lifts to four actual cycle vertices
 in their displayed cyclic order. -/
theorem alternating_vertices {α : Type*} (c : V → α) {w : List V} {A B : α}
    (h : [A, B, A, B].Sublist (w.map c)) :
    ∃ a b a' b' : V, c a = A ∧ c b = B ∧ c a' = A ∧ c b' = B ∧
      ∃ p₀ p₁ p₂ p₃ p₄ : List V,
        w = p₀ ++ a :: (p₁ ++ b :: (p₂ ++ a' :: (p₃ ++ b' :: p₄))) := by
  obtain ⟨v, hv, heq⟩ := List.sublist_map_iff.mp h
  have hlen : v.length = 4 := by simpa using (congrArg List.length heq).symm
  obtain ⟨a, b, a', b', rfl⟩ := List.length_eq_four.mp hlen
  have hc : c a = A ∧ c b = B ∧ c a' = A ∧ c b' = B := by
    simpa only [List.map_cons, List.map_nil, List.cons.injEq, and_true, eq_comm] using heq
  exact ⟨a, b, a', b', hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, sublist_four_split hv⟩

end Unimodular.CycleBounds
