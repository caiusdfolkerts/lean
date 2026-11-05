module

public import PaperVerification.PowerOperators
public import PaperVerification.PowerHarmonicWitness
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The actual Fischer pairing and the power-operator adjoint

The monomial Gram matrix has diagonal entry `∏ i, (a i)!`.  We prove
nondegeneracy in characteristic zero and the multiplication/differentiation
adjunction.  In particular the differential operator used for the resonant
witness is the adjoint of the paper's original power operator.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module
open scoped BigOperators

namespace PaperVerification.PowerFischerPairing

variable {K ι : Type*} [CommRing K] [Fintype ι]
local instance : DecidableEq ι := Classical.decEq ι
local notation "P" => MvPolynomial ι K

def factorialWeight (a : ι →₀ ℕ) : K := ∏ i : ι, ((a i).factorial : K)

theorem factorialWeight_step (a : ι →₀ ℕ) (i : ι) :
    factorialWeight (K := K) (a + Finsupp.single i 1) =
      (a i + 1 : K) * factorialWeight a := by
  classical
  unfold factorialWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i,
      (((a + Finsupp.single i 1 : ι →₀ ℕ) j).factorial : K)) =
      ∏ j ∈ Finset.univ.erase i, ((a j).factorial : K) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finsupp.add_apply,
      Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj), add_zero]
  rw [he]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem factorialWeight_mapDomain (σ : Equiv.Perm ι) (a : ι →₀ ℕ) :
    factorialWeight (K := K) (a.mapDomain σ) = factorialWeight a := by
  unfold factorialWeight
  calc
    _ = ∏ i : ι, (((a.mapDomain σ) (σ i)).factorial : K) := (Equiv.prod_comp σ _).symm
    _ = _ := by simp only [Finsupp.mapDomain_apply_of_injective σ.injective]

def fischer : P →ₗ[K] P →ₗ[K] K :=
  (basisMonomials ι K).constr K (fun a => factorialWeight (K := K) a • lcoeff K a)

@[simp] theorem fischer_monomial_one (a : ι →₀ ℕ) (p : P) :
    fischer (monomial a 1) p = factorialWeight a * p.coeff a := by
  change ((basisMonomials ι K).constr K
    (fun a => factorialWeight (K := K) a • lcoeff K a) ((basisMonomials ι K) a)) p = _
  rw [Basis.constr_basis]
  rfl

theorem fischer_eq_sum (p q : P) :
    fischer p q = ∑ a ∈ p.support,
      p.coeff a * (factorialWeight a * q.coeff a) := by
  rw [fischer, Basis.constr_apply]
  change (p.coeff.sum fun a b => b • (factorialWeight (K := K) a • lcoeff K a)) q = _
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    lcoeff_apply, smul_eq_mul, MvPolynomial.support]

theorem fischer_homogeneous_orthogonal (p q : P) (d e : ℕ)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) (hde : d ≠ e) :
    fischer p q = 0 := by
  rw [fischer_eq_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have had : a.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp (mem_support_iff.mp ha)
  rw [hq.coeff_eq_zero (fun h => hde (had.symm.trans h)), mul_zero, mul_zero]

theorem fischer_comm (p q : P) : fischer p q = fischer q p := by
  have he : (fischer : P →ₗ[K] P →ₗ[K] K) = fischer.flip := by
    apply (basisMonomials ι K).ext
    intro a
    apply (basisMonomials ι K).ext
    intro b
    simp only [coe_basisMonomials, LinearMap.flip_apply, fischer_monomial_one]
    by_cases h : a = b
    · subst b; rfl
    · simp [coeff_monomial, h, Ne.symm h]
  exact LinearMap.congr_fun (LinearMap.congr_fun he p) q

theorem fischer_homogeneousComponent_left (p q : P) (d : ℕ)
    (hq : q.IsHomogeneous d) :
    fischer (homogeneousComponent d p) q = fischer p q := by
  rw [fischer_comm (homogeneousComponent d p) q, fischer_comm p q,
    fischer_eq_sum, fischer_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have had : a.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hq (mem_support_iff.mp ha)
  rw [coeff_homogeneousComponent, if_pos had]

theorem fischer_rename (σ : Equiv.Perm ι) (p q : P) :
    fischer (rename σ p) (rename σ q) = fischer p q := by
  have he : (fischer.flip (rename σ q)).comp (rename σ).toLinearMap =
      fischer.flip q := by
    apply (basisMonomials ι K).ext
    intro a
    change fischer (rename σ (monomial a 1)) (rename σ q) =
      fischer (monomial a 1) q
    rw [rename_monomial, fischer_monomial_one, fischer_monomial_one,
      coeff_rename_mapDomain σ σ.injective q a, factorialWeight_mapDomain]
  exact LinearMap.congr_fun he p

theorem fischer_rename_right (σ : Equiv.Perm ι) (p q : P) :
    fischer p (rename σ q) = fischer (rename σ.symm p) q := by
  have he := fischer_rename σ (rename σ.symm p) q
  rw [rename_rename] at he
  have hcomp : (σ : ι → ι) ∘ σ.symm = id := by funext i; exact σ.apply_symm_apply i
  simpa only [hcomp, rename_id_apply] using he

theorem factorialWeight_ne_zero [IsDomain K] [CharZero K] (a : ι →₀ ℕ) :
    factorialWeight (K := K) a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (a i)

theorem fischer_right_nondegenerate [IsDomain K] [CharZero K]
    (q : P) (hq : ∀ p : P, fischer p q = 0) : q = 0 := by
  ext a
  have h := hq (monomial a 1)
  rw [fischer_monomial_one] at h
  simpa using (mul_eq_zero.mp h).resolve_left
    (factorialWeight_ne_zero a)

theorem fischer_left_nondegenerate [IsDomain K] [CharZero K]
    (p : P) (hp : ∀ q : P, fischer p q = 0) : p = 0 :=
  fischer_right_nondegenerate p (fun q => (fischer_comm q p).trans (hp q))

theorem fischer_X_mul (i : ι) (p q : P) :
    fischer (X i * p) q = fischer p (pderiv i q) := by
  have he : (fischer.flip q).comp (LinearMap.mulLeft K (X i)) =
      fischer.flip (pderiv i q) := by
    apply (basisMonomials ι K).ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, coe_basisMonomials,
      LinearMap.mulLeft_apply]
    have hm : X i * monomial a (1 : K) =
        monomial (a + Finsupp.single i 1) 1 := by
      rw [X, monomial_mul_monomial, one_mul, add_comm]
    rw [hm, fischer_monomial_one, fischer_monomial_one,
      factorialWeight_step, coeff_pderiv]
    push_cast
    ring
  exact LinearMap.congr_fun he p

theorem fischer_pderiv (i : ι) (p q : P) :
    fischer (pderiv i p) q = fischer p (X i*q) := by
  rw [fischer_comm, ← fischer_X_mul, fischer_comm]

theorem fischer_X_pow_mul (i : ι) (k : ℕ) (p q : P) :
    fischer (X i^k*p) q = fischer p ((pderiv i)^[k] q) := by
  induction k generalizing q with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, fischer_X_mul, ih, Function.iterate_succ_apply]

theorem fischer_euler (i : ι) (p q : P) :
    fischer (PowerOperators.euler i p) q =
      fischer p (PowerOperators.euler i q) := by
  rw [PowerOperators.euler_apply, fischer_X_mul, fischer_pderiv,
    PowerOperators.euler_apply]

/-- Adjointness is proved for the literal original differential operator,
not for a newly defined quotient or a substituted relation family. -/
theorem fischer_original (α : K) (k : ℕ) (p q : P) :
    fischer (PowerOperators.original (fun _ => (1 : K)) α k p) q =
      fischer p (PowerHarmonicWitness.adjointOriginal α k q) := by
  simp only [PowerOperators.original, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, one_smul, map_sum, LinearMap.sum_apply]
  simp_rw [fischer_X_pow_mul, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, fischer_euler]
  simp only [PowerHarmonicWitness.adjointOriginal, map_add, map_sum,
    C_mul', map_smul, PowerOperators.euler_apply,
    Function.iterate_succ_apply', Finset.sum_add_distrib, Finset.mul_sum,
    smul_eq_mul]

theorem resonant_witness_annihilates_original
    (α : K) (a b : ι) (q : ℕ)
    (hres : (Fintype.card ι : K) + α*(q+1 : ℕ) = 0)
    (k : ℕ) (hk : 0 < k) (p : P) :
    fischer (PowerOperators.original (fun _ => (1 : K)) α k p)
      (PowerHarmonicWitness.harmonicWitness a b q) = 0 := by
  rw [fischer_original,
    PowerHarmonicWitness.harmonicWitness_all_adjoint_zero α a b q hres k hk,
    map_zero]

end PaperVerification.PowerFischerPairing
