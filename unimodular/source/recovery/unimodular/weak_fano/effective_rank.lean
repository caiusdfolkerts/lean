module

public import Recovery.Unimodular.WeakFano.EffectiveConeDecision
public import Unimodular.RayHyperplanes
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Pointwise
open Set

namespace Unimodular.EffectiveRank

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

def signed (u : E → Lattice n) (s : Finset E) :
    {e // e ∈ s} ⊕ {e // e ∈ s} → Lattice n :=
  Sum.elim (fun e => u e.val) (fun e => -u e.val)

/-- Exact linear-span membership, computed through a symmetric integer cone. -/
def spanContains (u : E → Lattice n) (s : Finset E) (x : Lattice n) : Bool :=
  EffectiveConeDecision.contains (signed u s) x

/-- Each vector must avoid the span of the others. -/
def independentTest (u : E → Lattice n) (s : Finset E) : Prop :=
  ∀ e ∈ s, spanContains u (s.erase e) (u e) = false

instance (u : E → Lattice n) (s : Finset E) : Decidable (independentTest u s) := by
  unfold independentTest
  infer_instance

/-- Finite enumeration of all spanning independent subfamilies. -/
def rankEquals (u : E → Lattice n) (s : Finset E) (k : ℕ) : Prop :=
  ∃ t : Finset E, t ⊆ s ∧ independentTest u t ∧ t.card = k ∧
    ∀ e ∈ s, spanContains u t (u e) = true

instance (u : E → Lattice n) (s : Finset E) (k : ℕ) : Decidable (rankEquals u s k) := by
  unfold rankEquals
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

local notation "v[" u "]" => (fun e => embed (u e))

theorem signed_range (u : E → Lattice n) (s : Finset E) :
    Set.range v[signed u s] = v[u] '' (s : Set E) ∪ -(v[u] '' (s : Set E)) := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    cases e with
    | inl e => exact Or.inl ⟨e.val, e.property, rfl⟩
    | inr e =>
      apply Or.inr
      rw [Set.mem_neg]
      have he : -embed (signed u s (Sum.inr e)) = embed (u e.val) := by
        ext i
        simp [signed, embed]
      rw [he]
      exact ⟨e.val, e.property, rfl⟩
  · intro hx
    rcases hx with ⟨e, he, rfl⟩ | hx
    · exact ⟨Sum.inl ⟨e, he⟩, rfl⟩
    · rw [Set.mem_neg] at hx
      obtain ⟨e, he, heq⟩ := hx
      refine ⟨Sum.inr ⟨e, he⟩, ?_⟩
      calc
        embed (signed u s (Sum.inr ⟨e, he⟩)) = -embed (u e) := by
          ext i
          simp [signed, embed]
        _ = x := by
          change embed (u e) = -x at heq
          simpa only [neg_neg] using congrArg Neg.neg heq

theorem signed_cone_eq_span (u : E → Lattice n) (s : Finset E) :
    PointedCone.hull ℝ (Set.range v[signed u s]) =
      PointedCone.ofSubmodule (RayHyperplanes.raySpan v[u] s) := by
  have hsym : IsSelfNeg (Set.range v[signed u s]) := by
    rw [isSelfNeg_iff, signed_range]
    ext x
    simp only [Set.mem_neg, Set.mem_union, neg_neg, or_comm]
  have hsp : Submodule.span ℝ (Set.range v[signed u s]) =
      RayHyperplanes.raySpan v[u] s := by
    rw [signed_range]
    apply le_antisymm
    · apply Submodule.span_le.2
      intro x hx
      rcases hx with hx | hx
      · exact Submodule.subset_span hx
      · rw [Set.mem_neg] at hx
        have hm := (RayHyperplanes.raySpan v[u] s).neg_mem (Submodule.subset_span hx)
        change -(-x) ∈ RayHyperplanes.raySpan v[u] s at hm
        rw [neg_neg] at hm
        exact hm
    · apply Submodule.span_mono
      exact Set.subset_union_left
  exact (PointedCone.hull_eq_span_of_neg_eq ℝ hsym).trans (congrArg PointedCone.ofSubmodule hsp)

/-- Exact agreement with the actual real linear span. -/
theorem spanContains_iff (u : E → Lattice n) (s : Finset E) (x : Lattice n) :
    spanContains u s x = true ↔ embed x ∈ RayHyperplanes.raySpan v[u] s := by
  rw [spanContains, EffectiveConeDecision.contains_iff, signed_cone_eq_span]
  rfl

/-- The arithmetic independence test keeps the complete real meaning,
including repeated or zero vectors. -/
theorem independentTest_iff (u : E → Lattice n) (s : Finset E) :
    independentTest u s ↔ LinearIndepOn ℝ v[u] (s : Set E) := by
  constructor
  · intro h
    apply linearIndepOn_iff_notMem_span.2
    intro e he hm
    have hm' : embed (u e) ∈ RayHyperplanes.raySpan v[u] (s.erase e) := by
      simpa only [RayHyperplanes.raySpan, Finset.coe_erase] using hm
    have hh := (spanContains_iff u (s.erase e) (u e)).2 hm'
    rw [h e he] at hh
    exact Bool.false_ne_true hh
  · intro h e he
    cases hh : spanContains u (s.erase e) (u e) with
    | false => rfl
    | true =>
      exfalso
      apply (linearIndepOn_iff_notMem_span.1 h) e he
      simpa only [RayHyperplanes.raySpan, Finset.coe_erase] using
        (spanContains_iff u (s.erase e) (u e)).1 hh

theorem finrank_of_independent (u : E → Lattice n) (s : Finset E)
    (hs : LinearIndepOn ℝ v[u] (s : Set E)) :
    Module.finrank ℝ (RayHyperplanes.raySpan v[u] s) = s.card := by
  have he : Set.range (fun e : {e // e ∈ s} => embed (u e.val)) =
      v[u] '' (s : Set E) := by
    ext x
    constructor
    · rintro ⟨e, rfl⟩; exact ⟨e.val, e.property, rfl⟩
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he⟩, rfl⟩
  have h := finrank_span_eq_card hs
  change Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun e : {e // e ∈ s} => embed (u e.val)))) =
    Fintype.card {e // e ∈ s} at h
  rw [he] at h
  simpa only [RayHyperplanes.raySpan, Fintype.card_coe] using h

/-- The rank test is equivalent to the actual real dimension, uniformly for
every dimension and every finite integer matrix. Classical basis selection
occurs only in this erased correctness proof, never in the executable test. -/
theorem rankEquals_iff (u : E → Lattice n) (s : Finset E) (k : ℕ) :
    rankEquals u s k ↔ Module.finrank ℝ (RayHyperplanes.raySpan v[u] s) = k := by
  constructor
  · rintro ⟨t, hts, ht, hcard, hspan⟩
    have hLI := (independentTest_iff u t).1 ht
    have hsp : RayHyperplanes.raySpan v[u] t = RayHyperplanes.raySpan v[u] s := by
      apply le_antisymm
      · exact Submodule.span_mono (Set.image_mono hts)
      · apply Submodule.span_le.2
        rintro x ⟨e, he, rfl⟩
        exact (spanContains_iff u t (u e)).1 (hspan e he)
    rw [← hsp, finrank_of_independent u t hLI, hcard]
  · intro hk
    let hLI₀ : LinearIndepOn ℝ v[u] (∅ : Set E) := linearIndepOn_empty ℝ v[u]
    let T := hLI₀.extend (Set.empty_subset (s : Set E))
    let t : Finset E := T.toFinset
    have htset : (t : Set E) = T := Set.coe_toFinset T
    have hts : t ⊆ s := by
      intro e he
      apply hLI₀.extend_subset (Set.empty_subset (s : Set E))
      change e ∈ T
      rwa [← htset]
    have hLI : LinearIndepOn ℝ v[u] (t : Set E) := by
      rw [htset]
      exact hLI₀.linearIndepOn_extend _
    have hsp : RayHyperplanes.raySpan v[u] t = RayHyperplanes.raySpan v[u] s := by
      unfold RayHyperplanes.raySpan
      rw [htset]
      exact hLI₀.span_image_extend_eq_span_image _
    refine ⟨t, hts, (independentTest_iff u t).2 hLI, ?_, ?_⟩
    · rw [← finrank_of_independent u t hLI, hsp]
      exact hk
    · intro e he
      apply (spanContains_iff u t (u e)).2
      rw [hsp]
      exact Submodule.subset_span ⟨e, he, rfl⟩

end
end Unimodular.EffectiveRank

#print axioms Unimodular.EffectiveRank.rankEquals
#print axioms Unimodular.EffectiveRank.spanContains_iff
#print axioms Unimodular.EffectiveRank.independentTest_iff
#print axioms Unimodular.EffectiveRank.rankEquals_iff
#check Unimodular.EffectiveRank.rankEquals_iff
