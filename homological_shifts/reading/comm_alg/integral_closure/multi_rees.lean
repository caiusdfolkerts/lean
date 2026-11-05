import CommAlg.IntegralClosure.SemigroupAlgebra
import CommAlg.Polymatroid.MultiRank
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.BigOperators

/-! # The actual multi-Rees subalgebra and its homogeneous ideals

The definition is the ordinary subalgebra of a polynomial ring whose
multidegree-s coefficient lies in the product of ideal powers.
-/

noncomputable section

namespace CommAlg

open Classical Finset

variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

def powerProduct (I : J → Ideal R) (s : J →₀ ℕ) : Ideal R := ∏ j, (I j) ^ (s j)

@[simp] theorem powerProduct_zero (I : J → Ideal R) : powerProduct I 0 = ⊤ := by
  simp [powerProduct]

theorem powerProduct_add (I : J → Ideal R) (s t : J →₀ ℕ) :
    powerProduct I (s + t) = powerProduct I s * powerProduct I t := by
  simp only [powerProduct, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

def multiReesAlgebra (I : J → Ideal R) : Subalgebra R (MvPolynomial J R) where
  carrier := {p | ∀ s, p.coeff s ∈ powerProduct I s}
  zero_mem' := by simp
  one_mem' := by
    intro s
    by_cases hs : s = 0
    · subst s; simp
    · simp [MvPolynomial.coeff_one, hs, Ne.symm hs]
  add_mem' hp hq := fun s => by
    simpa only [MvPolynomial.coeff_add] using Ideal.add_mem _ (hp s) (hq s)
  mul_mem' hp hq := by
    intro s
    rw [MvPolynomial.coeff_mul]
    apply Ideal.sum_mem
    intro uv huv
    have he : uv.1 + uv.2 = s := Finset.mem_antidiagonal.mp huv
    have h := Ideal.mul_mem_mul (hp uv.1) (hq uv.2)
    rwa [← powerProduct_add, he] at h
  algebraMap_mem' r := by
    intro s
    change (MvPolynomial.C r).coeff s ∈ powerProduct I s
    by_cases hs : s = 0
    · subst s; simp
    · simp [MvPolynomial.coeff_C, hs, Ne.symm hs]

@[simp] theorem mem_multiReesAlgebra (I : J → Ideal R) (p : MvPolynomial J R) :
    p ∈ multiReesAlgebra I ↔ ∀ s, p.coeff s ∈ powerProduct I s := Iff.rfl

@[simp] theorem monomial_mem_multiReesAlgebra (I : J → Ideal R) (s : J →₀ ℕ) (r : R) :
    MvPolynomial.monomial s r ∈ multiReesAlgebra I ↔ r ∈ powerProduct I s := by
  constructor
  · intro h
    simpa using h s
  · intro h t
    by_cases ht : t = s
    · subst t; simpa using h
    · simp [MvPolynomial.coeff_monomial, ht, Ne.symm ht]

def multiReesIdeal (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) : Ideal (multiReesAlgebra I) where
  carrier := {p | ∀ s, p.val.coeff s ∈ K s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, MvPolynomial.coeff_add] using (K s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ K s
    rw [MvPolynomial.coeff_mul]
    apply Ideal.sum_mem
    intro uv huv
    have he : uv.1 + uv.2 = s := Finset.mem_antidiagonal.mp huv
    rw [← he]
    exact hact uv.1 uv.2 (Ideal.mul_mem_mul (r.property uv.1) (hp uv.2))

@[simp] theorem mem_multiReesIdeal (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) (p : multiReesAlgebra I) :
    p ∈ multiReesIdeal I K hact ↔ ∀ s, p.val.coeff s ∈ K s := Iff.rfl

section Polynomial

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k]

def reesDegree (e : J ⊕ V →₀ ℕ) : J →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp e).1

def ordinaryDegree (e : J ⊕ V →₀ ℕ) : V →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp e).2

@[simp] theorem reesDegree_apply (e : J ⊕ V →₀ ℕ) (j : J) : reesDegree e j = e (.inl j) := rfl

@[simp] theorem ordinaryDegree_apply (e : J ⊕ V →₀ ℕ) (v : V) : ordinaryDegree e v = e (.inr v) := rfl

theorem coeff_sumAlgEquiv (p : MvPolynomial (J ⊕ V) k) (s : J →₀ ℕ) (a : V →₀ ℕ) :
    (((MvPolynomial.sumAlgEquiv k J V) p).coeff s).coeff a =
      p.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)) := by
  change ((AddMonoidAlgebra.domCongr k k Finsupp.sumFinsuppAddEquivProdFinsupp p).coeff (s,a)) = _
  exact AddMonoidAlgebra.coeff_domCongr _ _ _

theorem coeff_flatten (p : MvPolynomial J (MvPolynomial V k)) (s : J →₀ ℕ) (a : V →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff
      (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)) = (p.coeff s).coeff a := by
  have h := coeff_sumAlgEquiv ((MvPolynomial.sumAlgEquiv k J V).symm p) s a
  simpa only [AlgEquiv.apply_symm_apply] using h.symm

theorem coeff_flatten_at (p : MvPolynomial J (MvPolynomial V k)) (e : J ⊕ V →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff e =
      (p.coeff (reesDegree e)).coeff (ordinaryDegree e) := by
  have h := coeff_flatten p (reesDegree e) (ordinaryDegree e)
  simpa only [reesDegree, ordinaryDegree, Prod.mk.eta, AddEquiv.symm_apply_apply] using h

def multiReesFlatten (I : J → Ideal (MvPolynomial V k)) :
    multiReesAlgebra I →+* MvPolynomial (J ⊕ V) k :=
  (MvPolynomial.sumAlgEquiv k J V).symm.toRingHom.comp (multiReesAlgebra I).val.toRingHom

theorem multiReesFlatten_injective (I : J → Ideal (MvPolynomial V k)) :
    Function.Injective (multiReesFlatten I) :=
  (MvPolynomial.sumAlgEquiv k J V).symm.injective.comp Subtype.val_injective

theorem multiReesFlatten_coeff (I : J → Ideal (MvPolynomial V k))
    (p : multiReesAlgebra I) (e : J ⊕ V →₀ ℕ) :
    (multiReesFlatten I p).coeff e = (p.val.coeff (reesDegree e)).coeff (ordinaryDegree e) :=
  coeff_flatten_at p.val e

theorem mem_polymatroid_multiRees (ρ : J → Polymatroid.RankFunction V)
    (p : MvPolynomial J (MvPolynomial V k)) :
    p ∈ multiReesAlgebra (fun j => Polymatroid.rankIdeal k (ρ j)) ↔
      ∀ e, ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff e ≠ 0 →
        Polymatroid.LowerFeasible (Polymatroid.multiRank ρ (reesDegree e)).lower (ordinaryDegree e) := by
  simp only [mem_multiReesAlgebra, powerProduct, ← Polymatroid.rankIdeal_multiRank]
  constructor
  · intro hp e he
    have hm := (Polymatroid.mem_monomialIdeal_iff _ _).mp (hp (reesDegree e))
    exact (Polymatroid.contains_rankBases_iff _ _).mp
      (hm _ (MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten_at] at he)))
  · intro hp s
    apply (Polymatroid.mem_monomialIdeal_iff _ _).mpr
    intro a ha
    let e := Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)
    have he : ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff e ≠ 0 := by
      rw [coeff_flatten]
      exact MvPolynomial.mem_support_iff.mp ha
    have h := hp e he
    have hs : reesDegree e = s := by simp [e, reesDegree]
    have ha' : ordinaryDegree e = a := by simp [e, ordinaryDegree]
    rw [hs, ha'] at h
    exact (Polymatroid.contains_rankBases_iff _ _).mpr h

end Polynomial

end CommAlg
