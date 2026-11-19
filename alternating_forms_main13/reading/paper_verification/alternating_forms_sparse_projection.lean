module

public import PaperVerification.AlternatingFormsFrobenius
public import PaperVerification.AlternatingFormsOddPencilRelations
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Sparse projections detecting both Frobenius syzygies

The first projection retains exactly the vertices `4j,4j+1` for `j<r`.
It kills the second path quadratic and sends the first to `r` disjoint pair
monomials. Its `r`th power is the nonzero factorial times their retained
exterior product. Reflection gives the corresponding certificate with the
two path quadrics interchanged.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

section PairedBasis

variable {I ι : Type*} [LinearOrder I] [Fintype ι] [DecidableEq ι]

/-- Pair products built from distinct basis generators are nonzero in the
actual exterior algebra. -/
theorem paired_basis_monomial_ne_zero (b : Module.Basis I K M) (u v : ι → I)
    (huv : Function.Injective (Sum.elim u v : ι ⊕ ι → I)) (P : Finset ι) :
    pairedMonomial (K := K) (fun i => b (u i)) (fun i => b (v i)) P ≠ 0 := by
  classical
  have hu : Function.Injective u := fun i j h => Sum.inl_injective (huv h)
  have hv : Function.Injective v := fun i j h => Sum.inr_injective (huv h)
  have hdis : List.Disjoint (P.toList.map u) (P.toList.map v) := by
    intro i hiu hiv
    obtain ⟨a, ha, hia⟩ := List.mem_map.mp hiu
    obtain ⟨c, hc, hic⟩ := List.mem_map.mp hiv
    have hbad : (Sum.inl a : ι ⊕ ι) = Sum.inr c := huv (hia.trans hic.symm)
    cases hbad
  have hnodup : (P.toList.map u ++ P.toList.map v).Nodup :=
    List.nodup_append.mpr ⟨P.nodup_toList.map hu, P.nodup_toList.map hv,
      fun a ha c hc heq => hdis ha (heq.symm ▸ hc)⟩
  have hperm : (P.toList.map u ++ P.toList.map v).Perm
      (P.toList.flatMap fun i => [u i, v i]) := by
    simpa only [← List.map_eq_flatMap, List.cons_append, List.nil_append] using
      List.flatMap_append_perm P.toList (fun i => [u i]) (fun i => [v i])
  have hn := exterior_basis_word_ne_zero b
    (P.toList.flatMap fun i => [u i, v i]) (hperm.nodup_iff.mp hnodup)
  have heq :
      (((P.toList.flatMap fun i => [u i, v i]).map b).map
        (ExteriorAlgebra.ι K)).prod =
      pairedMonomial (K := K) (fun i => b (u i)) (fun i => b (v i)) P := by
    simpa only [List.map_flatMap, List.map_cons, List.map_nil] using
      pair_word_product (K := K) (fun i => b (u i)) (fun i => b (v i)) P
  rwa [heq] at hn

end PairedBasis

section Sparse

variable {k r : ℕ}

/-- Retained left endpoint of the `j`th separated pair. -/
def sparsePathLeft (hr : 2*r ≤ k) (j : Fin r) : Fin (2*k+1) :=
  ⟨4*j.val, by have := j.isLt; omega⟩

def sparsePathRight (hr : 2*r ≤ k) (j : Fin r) : Fin (2*k+1) :=
  ⟨4*j.val+1, by have := j.isLt; omega⟩

theorem sparsePath_injective (hr : 2*r ≤ k) :
    Function.Injective
      (Sum.elim (sparsePathLeft hr) (sparsePathRight hr) : Fin r ⊕ Fin r → Fin (2*k+1)) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 4*a.val = 4*b.val at hv
      omega
    | inr b =>
      have hv := congrArg Fin.val h
      change 4*a.val = 4*b.val+1 at hv
      omega
  | inr a =>
    cases b with
    | inl b =>
      have hv := congrArg Fin.val h
      change 4*a.val+1 = 4*b.val at hv
      omega
    | inr b =>
      apply congrArg Sum.inr
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 4*a.val+1 = 4*b.val+1 at hv
      omega

def sparsePathKeep (r : ℕ) (i : Fin (2*k+1)) : Prop :=
  i.val / 4 < r ∧ i.val % 4 < 2

instance sparsePathKeep_decidable (r : ℕ) (i : Fin (2*k+1)) :
    Decidable (sparsePathKeep r i) := inferInstanceAs (Decidable (_ ∧ _))

/-- A literal coordinate projection, extended to the exterior algebra by
its universal property. -/
def sparsePathProjection (b : Module.Basis (Fin (2*k+1)) K M) (r : ℕ) : M →ₗ[K] M :=
  b.constr K (fun i => if sparsePathKeep r i then b i else 0)

def sparsePathExteriorProjection (b : Module.Basis (Fin (2*k+1)) K M) (r : ℕ) :
    ExteriorAlgebra K M →ₐ[K] ExteriorAlgebra K M :=
  ExteriorAlgebra.map (sparsePathProjection b r)

@[simp] theorem sparsePathProjection_basis (b : Module.Basis (Fin (2*k+1)) K M)
    (r : ℕ) (i : Fin (2*k+1)) :
    sparsePathProjection b r (b i) = if sparsePathKeep r i then b i else 0 :=
  b.constr_basis K _ i

@[simp] theorem sparsePathExteriorProjection_basis (b : Module.Basis (Fin (2*k+1)) K M)
    (r : ℕ) (i : Fin (2*k+1)) :
    sparsePathExteriorProjection b r (ExteriorAlgebra.ι K (b i)) =
      if sparsePathKeep r i then ExteriorAlgebra.ι K (b i) else 0 := by
  simp only [sparsePathExteriorProjection, ExteriorAlgebra.map_apply_ι,
    sparsePathProjection_basis]
  split_ifs <;> simp only [map_zero]

/-- No edge of the second matching has both endpoints retained. -/
theorem sparsePathProjection_second (b : Module.Basis (Fin (2*k+1)) K M) (r : ℕ) :
    sparsePathExteriorProjection b r
      (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M) = 0 := by
  rw [oddPathSecondQuadratic, matchingQuadratic_coe, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul, sparsePathExteriorProjection_basis, sparsePathExteriorProjection_basis]
  by_cases hi : sparsePathKeep r (oddPathMiddle i)
  · have hn : ¬sparsePathKeep r (oddPathSecondRight i) := by
      dsimp [sparsePathKeep, oddPathMiddle, oddPathSecondRight] at hi ⊢
      omega
    rw [if_neg hn, mul_zero]
  · rw [if_neg hi, zero_mul]

/-- The surviving terms of the first matching are precisely `i=2j` for
`j<r`, each with coefficient one. -/
theorem sparsePathProjection_first (b : Module.Basis (Fin (2*k+1)) K M)
    (hr : 2*r ≤ k) :
    sparsePathExteriorProjection b r
      (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M) =
        ∑ j : Fin r, ExteriorAlgebra.ι K (b (sparsePathLeft hr j)) *
          ExteriorAlgebra.ι K (b (sparsePathRight hr j)) := by
  classical
  let P : Fin k → Prop := fun i => i.val % 2 = 0 ∧ i.val / 2 < r
  rw [oddPathFirstQuadratic, matchingQuadratic_coe, map_sum]
  have hterm (i : Fin k) :
      sparsePathExteriorProjection b r
        (ExteriorAlgebra.ι K (b (oddPathFirstLeft i)) *
          ExteriorAlgebra.ι K (b (oddPathMiddle i))) =
      if P i then ExteriorAlgebra.ι K (b (oddPathFirstLeft i)) *
          ExteriorAlgebra.ι K (b (oddPathMiddle i)) else 0 := by
    rw [map_mul, sparsePathExteriorProjection_basis, sparsePathExteriorProjection_basis]
    by_cases hi : P i
    · have hl : sparsePathKeep r (oddPathFirstLeft i) := by
        dsimp [sparsePathKeep, oddPathFirstLeft, P] at hi ⊢; omega
      have hm : sparsePathKeep r (oddPathMiddle i) := by
        dsimp [sparsePathKeep, oddPathMiddle, P] at hi ⊢; omega
      rw [if_pos hi, if_pos hl, if_pos hm]
    · have hl : ¬sparsePathKeep r (oddPathFirstLeft i) := by
        dsimp [sparsePathKeep, oddPathFirstLeft, P] at hi ⊢; omega
      rw [if_neg hi, if_neg hl, zero_mul]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => (⟨i.val / 2,
    (Finset.mem_filter.mp hi).2.2⟩ : Fin r))
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi i' hi' heq
    apply Fin.ext
    have h₁ := (Finset.mem_filter.mp hi).2.1
    have h₂ := (Finset.mem_filter.mp hi').2.1
    have h₃ := congrArg Fin.val heq
    dsimp at h₃
    omega
  · intro j hj
    let i : Fin k := ⟨2*j.val, by have := j.isLt; omega⟩
    have hi : i ∈ Finset.univ.filter P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp [P, i]
      have := j.isLt
      omega
    refine ⟨i, hi, ?_⟩
    apply Fin.ext
    dsimp [i]
    omega
  · intro i hi
    have heven := (Finset.mem_filter.mp hi).2.1
    congr 3 <;> apply Fin.ext <;>
      dsimp [oddPathFirstLeft, oddPathMiddle, sparsePathLeft, sparsePathRight] <;> omega

/-- The first Frobenius cycle is detected by a projection killing `G`. -/
theorem sparsePathProjection_first_power_ne_zero
    (b : Module.Basis (Fin (2*k+1)) K M) (hr : 2*r ≤ k)
    (hfac : (r.factorial : K) ≠ 0) :
    sparsePathExteriorProjection b r
      ((oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M) ^ r) ≠ 0 := by
  rw [map_pow, sparsePathProjection_first b hr]
  have he := exterior_matching_pow_card (K := K)
    (fun j : Fin r => b (sparsePathLeft hr j))
    (fun j : Fin r => b (sparsePathRight hr j))
  simp only [Fintype.card_fin] at he
  rw [he]
  exact smul_ne_zero hfac
    (paired_basis_monomial_ne_zero b (sparsePathLeft hr) (sparsePathRight hr)
      (sparsePath_injective hr) Finset.univ)


/-- Reflection interchanges the second path quadratic with minus the
first, in every characteristic. -/
theorem oddPath_second_reflection (z : Fin (2*k+1) → M) :
    oddPathSecondQuadratic (K := K) (fun i => z i.rev) =
      -oddPathFirstQuadratic (K := K) z := by
  have h := oddPath_reflection (K := K) (fun i => z i.rev)
  have h' : oddPathFirstQuadratic (K := K) z =
      -oddPathSecondQuadratic (K := K) (fun i => z i.rev) := by
    simpa only [Fin.rev_rev] using h
  have hn := congrArg Neg.neg h'
  simp only [neg_neg] at hn
  exact hn.symm

/-- Two actual algebra maps detect the Frobenius powers separately. No
quotient independence or dimension conclusion is assumed. -/
theorem oddPath_frobenius_projection_certificates
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 2*(p-1) ≤ k) :
    ∃ π₁ π₂ : ExteriorAlgebra K M →ₐ[K] ExteriorAlgebra K M,
      π₁ (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M) = 0 ∧
      π₁ ((oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)^(p-1)) ≠ 0 ∧
      π₂ (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M) = 0 ∧
      π₂ ((oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M)^(p-1)) ≠ 0 := by
  let b' := b.reindex Fin.revPerm
  have hf' : oddPathFirstQuadratic (K := K) b' = -oddPathSecondQuadratic (K := K) b := by
    simpa only [b', Module.Basis.coe_reindex, Fin.revPerm_symm, Fin.revPerm_apply,
      Function.comp_def] using
      oddPath_reflection (K := K) b
  have hg' : oddPathSecondQuadratic (K := K) b' = -oddPathFirstQuadratic (K := K) b := by
    simpa only [b', Module.Basis.coe_reindex, Fin.revPerm_symm, Fin.revPerm_apply,
      Function.comp_def] using
      oddPath_second_reflection (K := K) b
  have hp := (Fact.out : p.Prime).two_le
  have hfac : ((p-1).factorial : K) ≠ 0 :=
    factorial_cast_ne_zero_of_lt_char p (p-1) (by omega)
  refine ⟨sparsePathExteriorProjection b (p-1),
    sparsePathExteriorProjection b' (p-1),
    sparsePathProjection_second b (p-1),
    sparsePathProjection_first_power_ne_zero b hk hfac, ?_, ?_⟩
  · have h := sparsePathProjection_second b' (p-1)
    rw [hg', Submodule.coe_neg, map_neg] at h
    exact neg_eq_zero.mp h
  · have h := sparsePathProjection_first_power_ne_zero b' hk hfac
    rw [hf', Submodule.coe_neg] at h
    intro hz
    have hz' : (sparsePathExteriorProjection b' (p-1)
        (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M))^(p-1) = 0 := by
      simpa only [map_pow] using hz
    apply h
    rw [map_pow, map_neg, neg_pow, hz', mul_zero]

end Sparse

end PaperVerification.AlternatingForms
