module

public import Papers.GraphicalZonotopes.PureEdgePartitions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

section Split
variable {J W : Type*} [Fintype J] [DecidableEq J]
variable [AddCommGroup W] [Module ℝ W]

def splitColumnFamily (v : J → W) (j₀ : J) (u : W) : Option J → W
  | none => u
  | some j => if j=j₀ then v j-u else v j

theorem splitColumnFamily_sum (v : J → W) (j₀ : J) (u : W) (c : Option J → ℝ) :
    (∑ j,c j • splitColumnFamily v j₀ u j)=
      (c none-c (some j₀)) • u+∑ j,c (some j) • v j := by
  rw [Fintype.sum_option]
  simp only [splitColumnFamily]
  have he : ∀ j,(if j=j₀ then v j-u else v j)=v j-(if j=j₀ then u else 0) := by
    intro j
    by_cases h : j=j₀ <;> simp [h]
  simp_rw [he,smul_sub]
  rw [sum_sub_distrib]
  have hs : (∑ j,c (some j) • (if j=j₀ then u else 0))=c (some j₀) • u := by
    simp [smul_ite]
  rw [hs,sub_smul]
  abel

theorem splitColumnFamily_independent (v : J → W) (hv : LinearIndependent ℝ v)
    (j₀ : J) (u : W) (hu : u∉Submodule.span ℝ (Set.range v)) :
    LinearIndependent ℝ (splitColumnFamily v j₀ u) := by
  have hi := hv.option hu
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  rw [splitColumnFamily_sum] at hc
  let d : Option J → ℝ := fun j => match j with
    | none => c none-c (some j₀)
    | some j => c (some j)
  have hd : (∑ j : Option J,d j • Option.casesOn' j u v)=0 := by
    rw [Fintype.sum_option]
    exact hc
  have hz := (Fintype.linearIndependent_iff.mp hi) d hd
  cases j with
  | none =>
    have h0 := hz none
    have hj := hz (some j₀)
    change c none-c (some j₀)=0 at h0
    change c (some j₀)=0 at hj
    linarith
  | some j => exact hz (some j)

theorem splitColumnFamily_preserves_sum (v : J → W) (j₀ : J) (u : W) (w : J → ℝ) :
    (∑ j : Option J,(Option.casesOn' j (w j₀) w) • splitColumnFamily v j₀ u j)=
      ∑ j,w j • v j := by
  rw [splitColumnFamily_sum]
  simp

theorem splitColumnFamily_span_mono (v : J → W) (j₀ : J) (u : W) :
    Submodule.span ℝ (Set.range v) ≤
      Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  change v j∈Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u))
  have hu : u∈Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u)) :=
    Submodule.subset_span ⟨none,rfl⟩
  have hj := Submodule.subset_span (R:=ℝ) (s:=Set.range (splitColumnFamily v j₀ u))
    (show splitColumnFamily v j₀ u (some j)∈Set.range (splitColumnFamily v j₀ u) from ⟨some j,rfl⟩)
  change splitColumnFamily v j₀ u (some j)∈Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u)) at hj
  by_cases h : j=j₀
  · have hh : v j-u∈Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u)) := by
      simpa only [splitColumnFamily,ite_eq_left h] using hj
    simpa only [sub_add_cancel] using (Submodule.add_mem _ hh hu)
  · simpa only [splitColumnFamily,ite_eq_right h] using hj

end Split

section PairBasis
variable {H : Type*} [Fintype H] [LinearOrder H]

theorem pairIn_card (C : Finset H) : Fintype.card (PairIn C)=C.card.choose 2 := by
  have hu : cliquePairs C C=univ := by
    ext e
    simp only [mem_cliquePairs,mem_univ,iff_true]
    exact e.2
  have h := cliquePairs_card C C (Subset.refl _)
  rwa [hu,card_univ] at h

theorem reference_pair_columns_independent (C : Finset H) (e₀ : PairIn C) :
    LinearIndependent ℝ (fun e : ↥((univ : Finset (PairIn C)).erase e₀) =>
      blockClass C (pairIndicator {e.1})) := by
  classical
  apply blockClass_linearIndependent_of_reference C e₀
  · rw [Fintype.linearIndependent_iff]
    intro c hc e
    have hv := congrFun hc e.1
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairIndicator,mem_singleton,
      Pi.zero_apply] at hv
    have heq : ∀ f : ↥((univ : Finset (PairIn C)).erase e₀),e.1=f.1 ↔ f=e :=
      fun f => ⟨fun h => Subtype.ext h.symm,fun h => congrArg Subtype.val h.symm⟩
    simp_rw [heq] at hv
    simpa using hv
  · intro e
    exact ite_eq_right (by simpa only [mem_singleton] using Ne.symm (mem_erase.mp e.2).1)

/-- Below the full block dimension, some genuine pair column lies outside
any given independent family. The argument counts a proved reference-pair
basis inside the actual response quotient. -/
theorem exists_pair_outside_span (C : Finset H) (e₀ : PairIn C)
    {J : Type*} [Fintype J] (v : J → ResponseQuotient H) (hv : LinearIndependent ℝ v)
    (hcard : Fintype.card J<C.card.choose 2-1) :
    ∃ e : PairIn C,blockClass C (pairIndicator {e})∉Submodule.span ℝ (Set.range v) := by
  classical
  by_contra hn
  have hall : ∀ e : PairIn C,blockClass C (pairIndicator {e})∈Submodule.span ℝ (Set.range v) := by
    intro e
    exact Classical.byContradiction (fun h => hn ⟨e,h⟩)
  let S := Submodule.span ℝ (Set.range v)
  let b : ↥((univ : Finset (PairIn C)).erase e₀) → S :=
    fun e => ⟨blockClass C (pairIndicator {e.1}),hall e.1⟩
  have hi : LinearIndependent ℝ b :=
    LinearIndependent.of_comp S.subtype (reference_pair_columns_independent C e₀)
  have hc := hi.fintype_card_le_finrank
  rw [finrank_span_eq_card hv] at hc
  simp only [Fintype.card_coe,card_erase_of_mem (mem_univ e₀),card_univ,pairIn_card] at hc
  omega

end PairBasis
end BooleanModule
end GraphicalZonotopes
