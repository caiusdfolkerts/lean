module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# The Laurent-monomial contraction in the projective Čech complex

A Laurent monomial occurs on an intersection of coordinate charts exactly
when all its negative exponents belong to the tuple of inverted coordinates.
The usual alternating tuple differential therefore preserves this support
condition. Insertion of a coordinate with nonnegative exponent is an explicit
contracting homotopy. If every exponent is negative, all terms below the
number of coordinates vanish literally.

These are statements about the actual alternating tuple complex, including
its support condition. The comparison with sections of twisting sheaves is
a separate obligation; this file does not call this complex sheaf cohomology.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperVerification.Segre.CechMonomials

open scoped BigOperators

variable {I K : Type*} [CommRing K]

/-- Tuple length is used, so length zero is the augmentation term. -/
abbrev RawCochain (I K : Type*) (q : ℕ) := (Fin q → I) → K

/-- The literal alternating deletion differential. -/
noncomputable def differential (q : ℕ) : RawCochain I K q →ₗ[K] RawCochain I K (q+1) where
  toFun f a := ∑ j : Fin (q+1), (-1 : K) ^ j.val * f (a ∘ j.succAbove)
  map_add' f g := by
    funext a
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c f := by
    funext a
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] theorem differential_apply (q : ℕ) (f : RawCochain I K q)
    (a : Fin (q+1) → I) :
    differential q f a=∑ j : Fin (q+1), (-1 : K)^j.val*f (a ∘ j.succAbove) := rfl

private theorem deletion_sign_cancel (q : ℕ) (i : Fin (q+2)) (j : Fin (q+1)) :
    (-1 : K)^i.val * (-1 : K)^j.val +
      (-1 : K)^(i.succAbove j).val * (-1 : K)^(j.predAbove i).val = 0 := by
  by_cases h : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ h,Fin.predAbove_of_castSucc_lt _ _ h]
    simp only [Fin.val_castSucc,Fin.val_pred]
    have hp : i.val-1+1=i.val := by have hh : j.val < i.val := h; omega
    conv_lhs => lhs; lhs; rw [← hp,pow_succ]
    ring
  · have h' : i ≤ j.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ h',Fin.predAbove_of_le_castSucc _ _ h']
    simp only [Fin.val_succ,Fin.coe_castPred,pow_succ]
    ring

/-- The literal alternating deletion differential squares to zero. -/
theorem differential_squared (q : ℕ) (f : RawCochain I K q) :
    differential (q+1) (differential q f)=0 := by
  classical
  funext a
  simp only [differential_apply,Finset.mul_sum,Pi.zero_apply]
  rw [← Finset.sum_product',Finset.univ_product_univ]
  refine Finset.sum_involution
    (fun p _ => (p.1.succAbove p.2,p.2.predAbove p.1)) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
  · rintro ⟨i,j⟩ _
    have he : (a ∘ (i.succAbove j).succAbove) ∘ (j.predAbove i).succAbove =
        (a ∘ i.succAbove) ∘ j.succAbove := by
      funext k
      simp only [Function.comp_apply,Fin.succAbove_succAbove_succAbove_predAbove]
    change (-1 : K)^i.val * ((-1 : K)^j.val * f ((a ∘ i.succAbove) ∘ j.succAbove)) +
      (-1 : K)^(i.succAbove j).val * ((-1 : K)^(j.predAbove i).val *
        f ((a ∘ (i.succAbove j).succAbove) ∘ (j.predAbove i).succAbove)) = 0
    rw [he,← mul_assoc,← mul_assoc,← add_mul,deletion_sign_cancel,zero_mul]
  · rintro ⟨i,j⟩ _ _ he
    exact Fin.succAbove_ne i j (congrArg Prod.fst he)
  · rintro ⟨i,j⟩ _
    simp only [Fin.succAbove_succAbove_predAbove,Fin.predAbove_predAbove_succAbove]

/-- Insertion of one coordinate is the Čech homotopy. -/
def contraction (v : I) (q : ℕ) : RawCochain I K (q+1) →ₗ[K] RawCochain I K q where
  toFun f a := f (Fin.cons v a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem contraction_apply (v : I) (q : ℕ) (f : RawCochain I K (q+1))
    (a : Fin q → I) : contraction v q f a=f (Fin.cons v a) := rfl

/-- The contracting identity, over every commutative ring and in every degree. -/
theorem contraction_identity (v : I) (q : ℕ) (f : RawCochain I K (q+1)) :
    contraction v (q+1) (differential (q+1) f) +
      differential q (contraction v q f) = f := by
  funext a
  change (∑ j : Fin (q+2), (-1 : K)^j.val*f (Fin.cons v a ∘ j.succAbove)) +
    (∑ j : Fin (q+1), (-1 : K)^j.val*f (Fin.cons v (a ∘ j.succAbove))) = f a
  rw [Fin.sum_univ_succ]
  have hz : Fin.cons v a ∘ (0 : Fin (q+2)).succAbove = a := by
    funext j
    simp only [Function.comp_apply,Fin.zero_succAbove,Fin.cons_succ]
  rw [hz]
  simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ,
    Fin.cons_comp_succ_succAbove]
  change f a + (∑ j : Fin (q+1), ((-1 : K)^j.val*(-1))*
    f (Fin.cons v (a ∘ j.succAbove))) +
      (∑ j : Fin (q+1), (-1 : K)^j.val*f (Fin.cons v (a ∘ j.succAbove))) = f a
  simp only [mul_neg_one,neg_mul,Finset.sum_neg_distrib]
  rw [add_assoc, neg_add_cancel, add_zero]

/-- Coefficients allowed only on tuples containing the negative support. -/
def supportedCochains (S : Set I) (q : ℕ) : Submodule K (RawCochain I K q) where
  carrier := {f | ∀ a, ¬ S ⊆ Set.range a → f a=0}
  zero_mem' := by intro a _; rfl
  add_mem' hf hg := by intro a ha; simp only [Pi.add_apply,hf a ha,hg a ha,add_zero]
  smul_mem' c f hf := by intro a ha; simp only [Pi.smul_apply,hf a ha,smul_zero]

theorem differential_mem_supported {S : Set I} {q : ℕ} {f : RawCochain I K q}
    (hf : f ∈ supportedCochains S q) :
    differential q f ∈ supportedCochains S (q+1) := by
  intro a ha
  rw [differential_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [hf (a ∘ j.succAbove) (by
    intro h
    apply ha
    intro x hx
    obtain ⟨k,hk⟩ := h hx
    exact ⟨j.succAbove k,hk⟩),mul_zero]

theorem contraction_mem_supported {S : Set I} (v : I) (hv : v ∉ S)
    {q : ℕ} {f : RawCochain I K (q+1)} (hf : f ∈ supportedCochains S (q+1)) :
    contraction v q f ∈ supportedCochains S q := by
  intro a ha
  apply hf
  intro h
  apply ha
  intro x hx
  obtain ⟨j,hj⟩ := h hx
  cases j using Fin.cases with
  | zero =>
    have he : v=x := hj
    exact False.elim (hv (he.symm ▸ hx))
  | succ k => exact ⟨k,hj⟩

/-- Every cocycle with proper negative support is a boundary in the augmented complex. -/
theorem exact_supported (S : Set I) (v : I) (hv : v ∉ S) (q : ℕ)
    (f : RawCochain I K (q+1)) (hf : f ∈ supportedCochains S (q+1))
    (hc : differential (q+1) f=0) :
    ∃ g : RawCochain I K q, g ∈ supportedCochains S q ∧ differential q g=f := by
  refine ⟨contraction v q f,contraction_mem_supported v hv hf,?_⟩
  have h := contraction_identity v q f
  simpa only [hc,map_zero,zero_add] using h

/-- The augmentation coefficient is zero whenever at least one exponent is negative. -/
theorem supported_zero_length {S : Set I} (hS : S.Nonempty)
    (f : RawCochain I K 0) (hf : f ∈ supportedCochains S 0) : f=0 := by
  funext a
  apply hf
  intro h
  obtain ⟨x,hx⟩ := hS
  obtain ⟨j,_⟩ := h hx
  exact Fin.elim0 j

/-- A proper nonempty negative support contributes no global cocycles. -/
theorem global_cocycle_eq_zero {S : Set I} (hS : S.Nonempty)
    (v : I) (hv : v ∉ S) (f : RawCochain I K 1)
    (hf : f ∈ supportedCochains S 1) (hc : differential 1 f=0) : f=0 := by
  obtain ⟨g,hg,hgf⟩ := exact_supported S v hv 0 f hf hc
  rw [supported_zero_length hS g hg,map_zero] at hgf
  exact hgf.symm

/-- A tuple too short to contain every coordinate supports no all-negative monomial. -/
theorem supported_univ_eq_zero [Fintype I] (q : ℕ) (hq : q<Fintype.card I)
    (f : RawCochain I K q) (hf : f ∈ supportedCochains (Set.univ : Set I) q) : f=0 := by
  funext a
  apply hf
  intro h
  have hs : Function.Surjective a := fun i => h (Set.mem_univ i)
  have hc := Fintype.card_le_of_surjective a hs
  simp only [Fintype.card_fin] at hc
  omega

/-- The actual Laurent exponent of a monomial; the total degree is an integer. -/
def negativeSupport (a : I → ℤ) : Set I := {i | a i<0}

theorem negativeSupport_nonempty_of_total_neg [Fintype I] (a : I → ℤ)
    (ha : ∑ i, a i<0) : (negativeSupport a).Nonempty := by
  by_contra h
  have hi : ∀ i, 0≤a i := by
    intro i
    by_contra hn
    exact h ⟨i,by exact lt_of_not_ge hn⟩
  exact (not_lt_of_ge (Finset.sum_nonneg (fun i _ => hi i))) ha

/-- All-negative exponent vectors have total degree at most minus the number of variables. -/
theorem total_le_neg_card_of_all_negative [Fintype I] (a : I → ℤ)
    (ha : ∀ i, a i<0) : ∑ i, a i≤-(Fintype.card I : ℤ) := by
  calc
    ∑ i, a i ≤ ∑ _i : I, (-1 : ℤ) := Finset.sum_le_sum (fun i _ => by have := ha i; omega)
    _ = -(Fintype.card I : ℤ) := by simp

/-- Degree at least `-N` on `P^N` ensures a nonnegative exponent in every monomial. -/
theorem exists_nonnegative_of_total_gt_neg_card [Fintype I] (a : I → ℤ)
    (ha : -(Fintype.card I : ℤ)<∑ i, a i) : ∃ i, 0≤a i := by
  by_contra h
  have hi : ∀ i, a i<0 := by
    intro i
    exact lt_of_not_ge (fun hi => h ⟨i,hi⟩)
  exact (not_lt_of_ge (total_le_neg_card_of_all_negative a hi)) ha

end PaperVerification.Segre.CechMonomials
