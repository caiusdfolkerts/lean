module

public import PaperVerification.PowerBoundary

/-!
# The exact Artin monomial bounds in the coordinate induction

Variables use zero-based `Fin n` indices, so the paper's bound
`a_i < m+i-1` is `a i < m+i.val`. Multiplication by the full product and
each boundary lift preserve precisely these bounds at the next induction
stage. The lemmas below concern the actual monomials in the polynomial ring.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

def IsArtinExponent (m : ℕ) (a : Fin n →₀ ℕ) : Prop :=
  ∀ i : Fin n, a i < m + i.val

def artinSpan (K : Type*) [Field K] (n m : ℕ) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K {p | ∃ a : Fin n →₀ ℕ,
    IsArtinExponent m a ∧ p = monomial a 1}

theorem monomial_mem_artinSpan (m : ℕ) (a : Fin n →₀ ℕ) (ha : IsArtinExponent m a) :
    monomial a (1 : K) ∈ artinSpan K n m :=
  Submodule.subset_span ⟨a, ha, rfl⟩

theorem artinSpan_zero (m : ℕ) : artinSpan K 0 m = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    have h := (artinSpan K 0 m).smul_mem r
      (monomial_mem_artinSpan m a (fun i => Fin.elim0 i))
    simpa only [smul_monomial, smul_eq_mul, mul_one] using h
  | add p q hp hq => exact (artinSpan K 0 m).add_mem hp hq

/-- Increasing every exponent by one shifts the full-support Artin block. -/
theorem IsArtinExponent.full_shift {m : ℕ} (hm : 0 < m)
    {a : Fin n →₀ ℕ} (ha : IsArtinExponent (m-1) a) :
    IsArtinExponent m (fullExponent + a) := by
  intro i
  have hi := ha i
  simp only [Finsupp.add_apply, fullExponent_apply]
  omega

theorem fullProduct_mul_mem_artinSpan (m : ℕ) (hm : 0 < m)
    (p : MvPolynomial (Fin n) K) (hp : p ∈ artinSpan K n (m-1)) :
    fullProduct * p ∈ artinSpan K n m := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a, ha, rfl⟩ := hp
    rw [fullProduct_eq_monomial, monomial_mul_monomial, one_mul]
    exact monomial_mem_artinSpan m _ (ha.full_shift hm)
  | zero => simpa only [mul_zero] using (artinSpan K n m).zero_mem
  | add p q _ _ hp hq => simpa only [mul_add] using (artinSpan K n m).add_mem hp hq
  | smul a p _ hp => simpa only [mul_smul_comm] using (artinSpan K n m).smul_mem a hp

def boundaryArtinExponent (i : Fin (n+1)) (a : Fin n →₀ ℕ) : Fin (n+1) →₀ ℕ :=
  boundaryExponent i + Finsupp.mapDomain i.succAbove a

@[simp] theorem boundaryArtinExponent_omitted (i : Fin (n+1)) (a : Fin n →₀ ℕ) :
    boundaryArtinExponent i a i = 0 := by
  rw [boundaryArtinExponent, Finsupp.add_apply, boundaryExponent_apply, if_neg (lt_irrefl i),
    zero_add, Finsupp.mapDomain_of_notMem_range]
  rintro ⟨j, hj⟩
  exact Fin.succAbove_ne i j hj

@[simp] theorem boundaryArtinExponent_image
    (i : Fin (n+1)) (a : Fin n →₀ ℕ) (j : Fin n) :
    boundaryArtinExponent i a (i.succAbove j) =
      (if i < i.succAbove j then 1 else 0) + a j := by
  rw [boundaryArtinExponent, Finsupp.add_apply, boundaryExponent_apply,
    Finsupp.mapDomain_apply_of_injective (f := i.succAbove)
      Fin.succAbove_right_injective]

theorem IsArtinExponent.boundary {m : ℕ} (hm : 0 < m)
    (i : Fin (n+1)) {a : Fin n →₀ ℕ} (ha : IsArtinExponent m a) :
    IsArtinExponent m (boundaryArtinExponent i a) := by
  intro j
  by_cases hji : j = i
  · subst j
    rw [boundaryArtinExponent_omitted]
    omega
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    rw [boundaryArtinExponent_image]
    have hk := ha k
    by_cases hki : k.castSucc < i
    · have hnot : ¬i < i.succAbove k := by
        rw [Fin.succAbove_of_castSucc_lt _ _ hki]
        exact not_lt_of_ge hki.le
      rw [if_neg hnot, zero_add, Fin.succAbove_of_castSucc_lt _ _ hki]
      exact hk
    · have hik : i ≤ k.castSucc := le_of_not_gt hki
      have hlt : i < i.succAbove k := (Fin.lt_succAbove_iff_le_castSucc i k).mpr hik
      rw [if_pos hlt, Fin.succAbove_of_le_castSucc _ _ hik]
      change 1+a k < m+(k.val+1)
      omega

theorem boundaryLift_monomial (i : Fin (n+1)) (a : Fin n →₀ ℕ) :
    boundaryLift i (monomial a (1 : K)) = monomial (boundaryArtinExponent i a) 1 := by
  rw [boundaryLift_apply, boundaryFactor_eq_monomial, rename_monomial,
    monomial_mul_monomial, one_mul]
  rfl

theorem boundaryLift_mem_artinSpan (m : ℕ) (hm : 0 < m) (i : Fin (n+1))
    (p : MvPolynomial (Fin n) K) (hp : p ∈ artinSpan K n m) :
    boundaryLift i p ∈ artinSpan K (n+1) m := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a, ha, rfl⟩ := hp
    rw [boundaryLift_monomial]
    exact monomial_mem_artinSpan m _ (ha.boundary hm i)
  | zero => simpa only [map_zero] using (artinSpan K (n+1) m).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using (artinSpan K (n+1) m).add_mem hp hq
  | smul a p _ hp => simpa only [map_smul] using (artinSpan K (n+1) m).smul_mem a hp

end PaperVerification.PowerOperators
