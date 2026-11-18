module

public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Relation

/-!
# The finite ray-walk argument

A generic line cuts each nondegenerate triangle in an interval. Crossing an
interior edge moves to the unique adjacent triangle, and the new interval
starts where the previous interval ends. Every forward walk ends at the same
boundary triangle. The theorem below proves the exact combinatorial assertion
used by that geometric argument: two such intervals cannot overlap in their
interiors. The geometric construction of the relation is a separate obligation.
-/

@[expose] public section

namespace NormalProjective.Planar

open Finset Relation

variable {α : Type*} [LinearOrder α]
variable {F : Type*} [Fintype F] [DecidableEq F]

theorem interval_reachable_order (lo hi : F → α) (hinterval : ∀ f, lo f < hi f)
    (R : F → F → Prop) (hstep : ∀ f g, R f g → hi f = lo g)
    {f g : F} (h : ReflTransGen R f g) : f = g ∨ hi f ≤ lo g := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail p q hprev hpq ih =>
    right
    rw [← hstep p q hpq]
    rcases ih with rfl | h
    · exact le_rfl
    · exact h.trans (hinterval p).le

theorem interval_reachable_hi_le (lo hi : F → α) (hinterval : ∀ f, lo f < hi f)
    (R : F → F → Prop) (hstep : ∀ f g, R f g → hi f = lo g)
    {f g : F} (h : ReflTransGen R f g) : hi f ≤ hi g := by
  rcases interval_reachable_order lo hi hinterval R hstep h with rfl | hfg
  · exact le_rfl
  · exact hfg.trans (hinterval g).le

theorem interval_reaches_terminal (lo hi : F → α) (hinterval : ∀ f, lo f < hi f)
    (R : F → F → Prop) (hstep : ∀ f g, R f g → hi f = lo g)
    (terminal : F → Prop) (hnext : ∀ f, ¬ terminal f → ∃ g, R f g) (f : F) :
    ∃ g, terminal g ∧ ReflTransGen R f g := by
  classical
  let S : Finset F := univ.filter (fun g => ReflTransGen R f g)
  have hfS : f ∈ S := by simp [S,ReflTransGen.refl]
  obtain ⟨g,hgS,hmax⟩ := exists_max_image S hi ⟨f,hfS⟩
  have hfg : ReflTransGen R f g := (mem_filter.mp hgS).2
  refine ⟨g,?_,hfg⟩
  by_contra hg
  obtain ⟨k,hgk⟩ := hnext g hg
  have hkS : k ∈ S := mem_filter.mpr ⟨mem_univ _,hfg.tail hgk⟩
  have hlt : hi g < hi k := by rw [hstep g k hgk]; exact hinterval k
  exact hlt.not_ge (hmax k hkS)

/-- The precise no-overlap conclusion of the ray walk. All assumptions concern
actual intervals and an actual relation; no injectivity of a drawing occurs in
the hypotheses. -/
theorem interval_chain_interiors_disjoint (lo hi : F → α)
    (hinterval : ∀ f, lo f < hi f) (R : F → F → Prop)
    (hstep : ∀ f g, R f g → hi f = lo g)
    (hpred : ∀ f g k, R f k → R g k → f = g)
    (terminal : F → Prop) (hterminal : ∀ f g, terminal f → terminal g → f = g)
    (hnext : ∀ f, ¬ terminal f → ∃ g, R f g)
    {f g : F} {x : α} (hf : lo f < x ∧ x < hi f) (hg : lo g < x ∧ x < hi g) : f = g := by
  classical
  by_contra hfg
  obtain ⟨a,ha,hfa⟩ := interval_reaches_terminal lo hi hinterval R hstep terminal hnext f
  obtain ⟨b,hb,hgb⟩ := interval_reaches_terminal lo hi hinterval R hstep terminal hnext g
  have hab := hterminal a b ha hb
  subst b
  let S : Finset F := univ.filter (fun k => ReflTransGen R f k ∧ ReflTransGen R g k)
  have haS : a ∈ S := mem_filter.mpr ⟨mem_univ _,hfa,hgb⟩
  obtain ⟨k,hkS,hmin⟩ := exists_min_image S hi ⟨a,haS⟩
  have hfk : ReflTransGen R f k := (mem_filter.mp hkS).2.1
  have hgk : ReflTransGen R g k := (mem_filter.mp hkS).2.2
  have hkf : k ≠ f := by
    intro h
    subst k
    rcases interval_reachable_order lo hi hinterval R hstep hgk with hgf | hgf
    · exact hfg hgf.symm
    · exact (not_lt_of_ge hgf) (hf.1.trans hg.2)
  have hkg : k ≠ g := by
    intro h
    subst k
    rcases interval_reachable_order lo hi hinterval R hstep hfk with hfg' | hfg'
    · exact hfg hfg'
    · exact (not_lt_of_ge hfg') (hg.1.trans hf.2)
  obtain ⟨p,hfp,hpk⟩ := hfk.cases_tail.resolve_left hkf
  obtain ⟨q,hgq,hqk⟩ := hgk.cases_tail.resolve_left hkg
  have hpq := hpred p q k hpk hqk
  subst q
  have hpS : p ∈ S := mem_filter.mpr ⟨mem_univ _,hfp,hgq⟩
  have hlt : hi p < hi k := by rw [hstep p k hpk]; exact hinterval k
  exact hlt.not_ge (hmin p hpS)

end NormalProjective.Planar

#print axioms NormalProjective.Planar.interval_chain_interiors_disjoint
