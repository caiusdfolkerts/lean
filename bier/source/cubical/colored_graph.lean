import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

/-! # The actual bipartite edge set of a properly two-colored graph -/

namespace Cubical.Bipartite

open Classical

variable {V : Type*} {G : SimpleGraph V}

abbrev Black (c : G.Coloring Bool) := {v : V // c v = false}
abbrev White (c : G.Coloring Bool) := {v : V // c v = true}
abbrev Edge (c : G.Coloring Bool) :=
  {e : Black c × White c // G.Adj e.1.val e.2.val}

def black (c : G.Coloring Bool) (e : Edge c) : Black c := e.val.1
def white (c : G.Coloring Bool) (e : Edge c) : White c := e.val.2

theorem color_eq_not_of_adj (c : G.Coloring Bool) {u v : V} (h : G.Adj u v) :
    c v = !(c u) := by
  have hc := c.valid h
  cases hu : c u <;> cases hv : c v <;> simp_all

theorem color_black_of_adj_white (c : G.Coloring Bool) (w : White c)
    {u : V} (h : G.Adj w.val u) : c u = false := by
  rw [color_eq_not_of_adj c h, w.property]
  rfl

theorem color_white_of_adj_black (c : G.Coloring Bool) (b : Black c)
    {u : V} (h : G.Adj b.val u) : c u = true := by
  rw [color_eq_not_of_adj c h, b.property]
  rfl

def vertexEquiv (c : G.Coloring Bool) : V ≃ (Black c ⊕ White c) where
  toFun v := if h : c v = false then Sum.inl ⟨v, h⟩
    else Sum.inr ⟨v, by cases h' : c v <;> simp_all⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv v := by by_cases h : c v = false <;> simp [h]
  right_inv v := by rcases v with ⟨v, hv⟩ | ⟨v, hv⟩ <;> simp [hv]

theorem card_vertices [Fintype V] (c : G.Coloring Bool) :
    Fintype.card (Black c) + Fintype.card (White c) = Fintype.card V := by
  simpa using (Fintype.card_congr (vertexEquiv c)).symm

def edgeToUnoriented (c : G.Coloring Bool) (e : Edge c) : G.edgeSet :=
  ⟨s(e.val.1.val, e.val.2.val), e.property⟩

theorem edgeToUnoriented_bijective (c : G.Coloring Bool) :
    Function.Bijective (edgeToUnoriented c) := by
  constructor
  · rintro ⟨⟨b, w⟩, hbw⟩ ⟨⟨b', w'⟩, hbw'⟩ h
    have heq : s(b.val, w.val) = s(b'.val, w'.val) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp heq with ⟨hb, hw⟩ | ⟨hbw, hwb⟩
    · exact Subtype.ext (Prod.ext (Subtype.ext hb) (Subtype.ext hw))
    · have hbad := congrArg c hbw
      rw [b.property, w'.property] at hbad
      cases hbad
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      change G.Adj u v at he
      have hne := c.valid he
      cases hu : c u <;> cases hv : c v
      · exact False.elim (hne (hu.trans hv.symm))
      · exact ⟨⟨(⟨u, hu⟩, ⟨v, hv⟩), he⟩, rfl⟩
      · exact ⟨⟨(⟨v, hv⟩, ⟨u, hu⟩), he.symm⟩, Subtype.ext Sym2.eq_swap⟩
      · exact False.elim (hne (hu.trans hv.symm))

noncomputable def edgeEquiv (c : G.Coloring Bool) : Edge c ≃ G.edgeSet :=
  Equiv.ofBijective (edgeToUnoriented c) (edgeToUnoriented_bijective c)

theorem card_edges [Fintype V] (c : G.Coloring Bool) :
    Fintype.card (Edge c) = Fintype.card G.edgeSet :=
  Fintype.card_congr (edgeEquiv c)

theorem white_injective_at_black (c : G.Coloring Bool) (b : Black c) :
    Function.Injective (fun e : {e : Edge c // black c e = b} => white c e.val) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (e.property.trans f.property.symm) h

def swapColoring (c : G.Coloring Bool) : G.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun v => !(c v)) (fun {_ _} h => by
    intro heq
    apply c.valid h
    simpa only [Bool.not_not] using congrArg Bool.not heq)

def swappedBlackEquiv (c : G.Coloring Bool) : Black (swapColoring c) ≃ White c :=
  Equiv.subtypeEquivRight fun v => by
    change (Bool.not (c v) = false) ↔ c v = true
    cases c v <;> simp

def swappedWhiteEquiv (c : G.Coloring Bool) : White (swapColoring c) ≃ Black c :=
  Equiv.subtypeEquivRight fun v => by
    change (Bool.not (c v) = true) ↔ c v = false
    cases c v <;> simp

end Cubical.Bipartite
