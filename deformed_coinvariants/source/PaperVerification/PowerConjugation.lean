module

public import PaperVerification.PowerSpanning
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# The actual diagonal conjugation of the two power families

The diagonal operator is the product of the coordinate Euler factors.  Its
invertibility uses all nonnegative exponents: nonresonance handles the tail,
and the additional hypothesis in (2.3) handles the finitely many smaller
exponents.  The hit spaces below are spans of operator images, not ideals.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K ι : Type*} [Field K] [Fintype ι]
local instance : DecidableEq ι := Classical.decEq ι

def diagonalWeight (c : ι → K) (lam : K) (a : ι →₀ ℕ) : K :=
  ∏ i, (c i + lam * (a i : K))

theorem coordinate_factor_ne_zero {c : ι → K} {lam : K} {m : ℕ}
    (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0)
    (i : ι) (a : ℕ) : c i + lam * (a : K) ≠ 0 := by
  by_cases ha : a < m
  · exact hlow i a ha
  · simpa using hnr {i} (by simp) a (by simpa using Nat.le_of_not_gt ha)

theorem diagonalWeight_ne_zero {c : ι → K} {lam : K} {m : ℕ}
    (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0)
    (a : ι →₀ ℕ) : diagonalWeight c lam a ≠ 0 := by
  unfold diagonalWeight
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    coordinate_factor_ne_zero hnr hlow i (a i)

def diagonalEquiv (c : ι → K) (lam : K)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) :
    MvPolynomial ι K ≃ₗ[K] MvPolynomial ι K :=
  (basisMonomials ι K).equiv
    ((basisMonomials ι K).isUnitSMul (w := diagonalWeight c lam)
      (fun a => isUnit_iff_ne_zero.mpr
        ((Finset.prod_ne_zero_iff (s := Finset.univ)).mpr fun i _ => h i (a i))))
    (Equiv.refl _)

@[simp] theorem diagonalEquiv_monomial (c : ι → K) (lam : K)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) (a : ι →₀ ℕ) :
    diagonalEquiv c lam h (monomial a 1) =
      diagonalWeight c lam a • monomial a 1 := by
  change (basisMonomials ι K).equiv _ _ ((basisMonomials ι K) a) = _
  rw [Module.Basis.equiv_apply, Module.Basis.isUnitSMul_apply]
  rfl

theorem diagonalWeight_step (c : ι → K) (lam : K) (a : ι →₀ ℕ)
    (i : ι) (k : ℕ) :
    diagonalWeight c lam (a + Finsupp.single i k) * (c i + lam * (a i : K)) =
      diagonalWeight c lam a * (c i + lam * ((a i + k : ℕ) : K)) := by
  classical
  have hrest :
      (∏ j ∈ Finset.univ.erase i, (c j + lam * ((a + Finsupp.single i k) j : K))) =
        ∏ j ∈ Finset.univ.erase i, (c j + lam * (a j : K)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Finsupp.add_apply, Finsupp.single_eq_of_ne hji]
  have ha := Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun j => c j + lam * (a j : K)) (Finset.mem_univ i)
  have hb := Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun j => c j + lam * ((a + Finsupp.single i k) j : K))
    (Finset.mem_univ i)
  simp only [diagonalWeight]
  rw [← ha, ← hb, hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  ring

theorem euler_monomial_one (i : ι) (a : ι →₀ ℕ) :
    euler (R := K) i (monomial a 1) = (a i : K) • monomial a 1 := by
  rw [euler_apply, X_mul_pderiv_monomial]
  simp [Nat.cast_smul_eq_nsmul]

theorem component_monomial_one (c lam : K) (i : ι) (k : ℕ) (a : ι →₀ ℕ) :
    component c lam i k (monomial a 1) =
      (c + lam * ((a i + k : ℕ) : K)) • monomial (a + Finsupp.single i k) 1 := by
  rw [component_apply, euler_monomial_one, smul_smul, ← add_smul,
    mul_smul_comm, mul_comm (X i ^ k), ← monomial_add_single]
  congr 1
  push_cast
  ring

theorem original_monomial_one (c : ι → K) (lam : K) (k : ℕ) (a : ι →₀ ℕ) :
    original c lam k (monomial a 1) =
      ∑ i, (c i + lam * (a i : K)) • monomial (a + Finsupp.single i k) 1 := by
  simp only [original, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.mulLeft_apply, euler_monomial_one, smul_smul, ← add_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul_comm, mul_comm (X i ^ k), ← monomial_add_single]

/-- The intertwining identity holds for every polynomial and every index. -/
theorem diagonalEquiv_original (c : ι → K) (lam : K)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) (k : ℕ)
    (p : MvPolynomial ι K) :
    diagonalEquiv c lam h (original c lam k p) =
      reversed c lam k (diagonalEquiv c lam h p) := by
  have he : (diagonalEquiv c lam h).toLinearMap.comp (original c lam k) =
      (reversed c lam k).comp (diagonalEquiv c lam h).toLinearMap := by
    apply (basisMonomials ι K).ext
    intro a
    change diagonalEquiv c lam h (original c lam k (monomial a 1)) =
      reversed c lam k (diagonalEquiv c lam h (monomial a 1))
    rw [original_monomial_one, map_sum, diagonalEquiv_monomial, map_smul,
      reversed_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, diagonalEquiv_monomial, component_monomial_one, smul_smul,
      smul_smul]
    congr 1
    simpa only [mul_comm] using diagonalWeight_step c lam a i k
  exact LinearMap.congr_fun he p

def originalTailHit (c : ι → K) (lam : K) (m : ℕ) :
    Submodule K (MvPolynomial ι K) :=
  Submodule.span K {p | ∃ k, m ≤ k ∧ ∃ q, p = original c lam k q}

/-- The image of the genuine homogeneous polynomial piece in the original
joint-image quotient. The definition also applies at resonant parameters. -/
def originalTailQuotientDegree (c : ι → K) (lam : K) (m d : ℕ) :
    Submodule K (MvPolynomial ι K ⧸ originalTailHit c lam m) :=
  (homogeneousSubmodule ι K d).map (originalTailHit c lam m).mkQ

theorem diagonalEquiv_map_originalTailHit (c : ι → K) (lam : K)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) (m : ℕ) :
    (originalTailHit c lam m).map (diagonalEquiv c lam h).toLinearMap =
      tailHit c lam m := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, q, rfl⟩
    change diagonalEquiv c lam h (original c lam k q) ∈ tailHit c lam m
    rw [diagonalEquiv_original]
    exact Submodule.subset_span ⟨k, hk, diagonalEquiv c lam h q, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, q, rfl⟩
    refine Submodule.mem_map.mpr
      ⟨original c lam k ((diagonalEquiv c lam h).symm q),
        Submodule.subset_span ⟨k, hk, _, rfl⟩, ?_⟩
    simp only [LinearEquiv.coe_toLinearMap, diagonalEquiv_original,
      LinearEquiv.apply_symm_apply]

theorem diagonalEquiv_map_artinSpan {n : ℕ} (c : Fin n → K) (lam : K)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) (m : ℕ) :
    (artinSpan K n m).map (diagonalEquiv c lam h).toLinearMap =
      artinSpan K n m := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change diagonalEquiv c lam h (monomial a 1) ∈ artinSpan K n m
    rw [diagonalEquiv_monomial]
    exact (artinSpan K n m).smul_mem _ (monomial_mem_artinSpan m a ha)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    have hw : diagonalWeight c lam a ≠ 0 := by
      unfold diagonalWeight
      exact Finset.prod_ne_zero_iff.mpr fun i _ => h i (a i)
    refine Submodule.mem_map.mpr ⟨(diagonalWeight c lam a)⁻¹ • monomial a 1,
      (artinSpan K n m).smul_mem _ (monomial_mem_artinSpan m a ha), ?_⟩
    simp only [LinearEquiv.coe_toLinearMap, map_smul, diagonalEquiv_monomial,
      smul_smul, inv_mul_cancel₀ hw, one_smul]

/-- The same full Artin spanning result for the original family, under precisely
the additional low-exponent conditions in equation (2.3). -/
theorem originalTailHit_sup_artinSpan_eq_top {n : ℕ}
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0) :
    originalTailHit c lam m ⊔ artinSpan K n m = ⊤ := by
  let h := coordinate_factor_ne_zero hnr hlow
  apply (Submodule.map_eq_top_iff (e := diagonalEquiv c lam h)).mp
  rw [Submodule.map_sup, diagonalEquiv_map_originalTailHit,
    diagonalEquiv_map_artinSpan]
  exact tailHit_sup_artinSpan_eq_top c lam m hm hnr

/-- Sufficiency for the spanning clause of Theorem 1.1, with exactly the full
exceptional set in the paper. Independence and characters are not asserted here. -/
theorem original_artin_spanning_outside_exceptional [CharZero K] {n : ℕ}
    (α : K) (hα : α ∉ exceptionalSet K n) :
    originalTailHit (fun _ : Fin n => (1 : K)) α 1 ⊔ artinSpan K n 1 = ⊤ := by
  apply originalTailHit_sup_artinSpan_eq_top _ _ _ (by omega)
  · apply (nonresonant_one_iff α).mpr
    simpa using hα
  · intro i a ha
    have : a = 0 := by omega
    simp [this]

end PaperVerification.PowerOperators
