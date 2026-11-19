module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The colored-edge estimate used in the cohomology gap

Weights of an exterior power of a direct sum of alternating two-form
representations are represented by distinct colored edges.  This file proves
the complete counting estimate for such edge sets.  The final theorem is the
numerical implication used after Borel--Weil--Bott in Lemma 2.1; this file
does not assert that the Borel--Weil--Bott identification has been formalized.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

section Incidence

variable {ι C : Type*} [LinearOrder ι] [Fintype C]

/-- An edge is stored with its color and its two endpoints.  Distinctness
is the `Finset` condition; the theorem below requires strictly ordered
endpoints, so there are neither loops nor two orientations of one edge. -/
abbrev ColoredEdge (C ι : Type*) := C × (ι × ι)

/-- The vertex weight of a set of colored edges. -/
def coloredVertexWeight (E : Finset (ColoredEdge C ι)) (v : ι) : ℕ :=
  ∑ e ∈ E, ((if e.2.1 = v then 1 else 0) + (if e.2.2 = v then 1 else 0))

/-- Double counting vertex incidences in an arbitrary vertex subset. -/
theorem sum_coloredVertexWeight (E : Finset (ColoredEdge C ι)) (P : Finset ι) :
    ∑ v ∈ P, coloredVertexWeight E v =
      ∑ e ∈ E, ((if e.2.1 ∈ P then 1 else 0) + (if e.2.2 ∈ P then 1 else 0)) := by
  classical
  unfold coloredVertexWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_add_distrib]
  simp [eq_comm]

/-- There are at most `m * choose(ℓ,2)` selected edges internal to a set
of `ℓ` vertices, where `m` is the total number of available colors. -/
theorem card_internal_coloredEdges_le (E : Finset (ColoredEdge C ι))
    (hE : ∀ e ∈ E, e.2.1 < e.2.2) (P : Finset ι) :
    (E.filter (fun e => e.2.1 ∈ P ∧ e.2.2 ∈ P)).card ≤
      Fintype.card C * P.card.choose 2 := by
  classical
  have hsub : E.filter (fun e => e.2.1 ∈ P ∧ e.2.2 ∈ P) ⊆
      Finset.univ ×ˢ ((P ×ˢ P).filter (fun e => e.1 < e.2)) := by
    intro e he
    obtain ⟨he, hfirst, hsecond⟩ := Finset.mem_filter.mp he
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hfirst, hsecond⟩, hE e he⟩⟩
  calc
    _ ≤ (Finset.univ ×ˢ ((P ×ˢ P).filter (fun e => e.1 < e.2))).card :=
      Finset.card_le_card hsub
    _ = _ := by rw [Finset.card_product, Finset.card_univ, Finset.card_product_filter_lt]

/-- The colored-edge weight estimate, with no restriction on the number
of vertices, colors, selected edges, or the chosen vertex subset. -/
theorem coloredEdge_weight_bound (E : Finset (ColoredEdge C ι))
    (hE : ∀ e ∈ E, e.2.1 < e.2.2) (P : Finset ι) :
    ∑ v ∈ P, coloredVertexWeight E v ≤
      E.card + Fintype.card C * P.card.choose 2 := by
  classical
  rw [sum_coloredVertexWeight]
  calc
    _ ≤ ∑ e ∈ E, (1 + if e.2.1 ∈ P ∧ e.2.2 ∈ P then 1 else 0) := by
      apply Finset.sum_le_sum
      intro e he
      by_cases hfirst : e.2.1 ∈ P <;>
        by_cases hsecond : e.2.2 ∈ P <;> simp [hfirst, hsecond]
    _ = E.card + (E.filter (fun e => e.2.1 ∈ P ∧ e.2.2 ∈ P)).card := by
      simp [Finset.sum_add_distrib, Finset.sum_boole]
    _ ≤ E.card + Fintype.card C * P.card.choose 2 :=
      Nat.add_le_add_left (card_internal_coloredEdges_le E hE P) _

end Incidence

/-- The triangle-number identity in the division-free form used to cancel
the two copies of the internal-edge bound. -/
theorem two_mul_choose_two_add (ℓ : ℕ) : 2 * ℓ.choose 2 + ℓ = ℓ * ℓ := by
  cases ℓ with
  | zero => simp
  | succ ℓ =>
    have h := Nat.add_one_mul_choose_eq ℓ 1
    simp only [Nat.choose_one_right] at h
    nlinarith

/-- The full numerical conclusion of the colored-edge argument in Lemma
2.1.  The hypotheses state the actual selected-edge realization and the
lower bound supplied by the crossed Bott entries; no rank inequality or
desired cohomology vanishing is assumed. -/
theorem twoColoredEdges_cohomology_gap
    {ι : Type*} [LinearOrder ι] (E : Finset (ColoredEdge (Fin 2) ι))
    (hE : ∀ e ∈ E, e.2.1 < e.2.2) (P : Finset ι)
    (d r : ℕ)
    (hlower : ∀ v ∈ P, d + P.card + r ≤ coloredVertexWeight E v) :
    P.card * d + (r + 1) * P.card ≤ E.card := by
  have hsum : P.card * (d + P.card + r) ≤ ∑ v ∈ P, coloredVertexWeight E v := by
    simpa using Finset.sum_le_sum hlower
  have hupper := coloredEdge_weight_bound E hE P
  simp only [Fintype.card_fin] at hupper
  have hchoose := two_mul_choose_two_add P.card
  nlinarith

end PaperVerification.AlternatingForms
