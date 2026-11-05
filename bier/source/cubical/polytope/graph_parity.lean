import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Bipartition from connected descending square fans

This graph theorem isolates the finite-descent argument needed for the
geometric bipartition proof. Its hypotheses explicitly describe descending
square fans; the separate geometric work must establish them for polytopes.
-/

namespace Cubical

variable {V : Type*}

/-- Two lower neighbors are related if they share a vertex below the peak. -/
def LowerSquareRelation (G : SimpleGraph V) (height : V → ℕ) (v a b : V) : Prop :=
  height a < height v ∧ height b < height v ∧
    ∃ z, height z < height v ∧ G.Adj a z ∧ G.Adj b z

open Classical in
noncomputable def descentColor (G : SimpleGraph V) (height : V → ℕ) (v : V) : Bool :=
  if h : ∃ u, G.Adj v u ∧ height u < height v then
    !(descentColor G height (Classical.choose h))
  else false
termination_by height v
decreasing_by exact (Classical.choose_spec h).2

private theorem bool_eq_of_ne_common {a b c : Bool} (hac : a ≠ c) (hbc : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Descending square-fan connectivity forces a proper two-coloring. -/
theorem descentColor_proper (G : SimpleGraph V) (height : V → ℕ)
    (hne : ∀ ⦃u v⦄, G.Adj u v → height u ≠ height v)
    (hfan : ∀ v a b, G.Adj v a → G.Adj v b →
      height a < height v → height b < height v →
      Relation.ReflTransGen (LowerSquareRelation G height v) a b) :
    ∀ ⦃u v⦄, G.Adj u v → descentColor G height u ≠ descentColor G height v := by
  classical
  have hdown : ∀ v, ∀ u, height u < height v → G.Adj v u →
      descentColor G height v ≠ descentColor G height u := by
    intro v
    induction v using (measure height).wf.induction with
    | h v ih =>
      intro u hu huv
      have hex : ∃ a, G.Adj v a ∧ height a < height v := ⟨u, huv, hu⟩
      let a := Classical.choose hex
      have hav : G.Adj v a := (Classical.choose_spec hex).1
      have ha : height a < height v := (Classical.choose_spec hex).2
      have hprev : ∀ p q, height p < height v → height q < height v → G.Adj p q →
          descentColor G height p ≠ descentColor G height q := by
        intro p q hp hq hpq
        rcases lt_or_gt_of_ne (hne hpq) with hpq' | hqp'
        · exact (ih q hq p hpq' hpq.symm).symm
        · exact ih p hp q hqp' hpq
      have hpath := hfan v a u hav huv ha hu
      have equal_along : ∀ {p q},
          Relation.ReflTransGen (LowerSquareRelation G height v) p q →
          descentColor G height p = descentColor G height q := by
        intro p q h
        induction h with
        | refl => rfl
        | tail _ hstep hsame =>
          rcases hstep with ⟨hp, hq, z, hz, hpz, hqz⟩
          have hcp := hprev _ z hp hz hpz
          have hcq := hprev _ z hq hz hqz
          exact hsame.trans (bool_eq_of_ne_common hcp hcq)
      have hsame := equal_along hpath
      rw [descentColor, dif_pos hex, ← hsame]
      simp [a]
  intro u v huv
  rcases lt_or_gt_of_ne (hne huv) with huv' | hvu'
  · exact (hdown v u huv' huv.symm).symm
  · exact hdown u v hvu' huv

theorem colorable_two_of_descending_square_fans (G : SimpleGraph V) (height : V → ℕ)
    (hne : ∀ ⦃u v⦄, G.Adj u v → height u ≠ height v)
    (hfan : ∀ v a b, G.Adj v a → G.Adj v b →
      height a < height v → height b < height v →
      Relation.ReflTransGen (LowerSquareRelation G height v) a b) :
    G.Colorable 2 := by
  let C : G.Coloring Bool :=
    SimpleGraph.Coloring.mk (descentColor G height)
      (fun {_ _} h => descentColor_proper G height hne hfan h)
  simpa using C.colorable

end Cubical
