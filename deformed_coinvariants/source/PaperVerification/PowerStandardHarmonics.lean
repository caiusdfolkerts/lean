module

public import PaperVerification.PowerHarmonicQuotient
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The full standard space of resonant harmonic functionals

The domain is the actual coordinate-sum-zero subspace of the permutation
module. Multiplication of its linear polynomial by a power of the sum of
the variables is injective, homogeneous, and commutes with permutations.
At resonance the whole space, not just one chosen polynomial, gives an
injective map into the dual of the literal differential quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module
open scoped BigOperators

namespace PaperVerification.PowerStandardHarmonics

variable {K ι : Type*} [Field K] [Fintype ι]
local instance : DecidableEq ι := Classical.decEq ι
local notation "P" => MvPolynomial ι K

def coordinateSum : (ι → K) →ₗ[K] K := ∑ i : ι, LinearMap.proj i

@[simp] theorem coordinateSum_apply (v : ι → K) :
    coordinateSum v = ∑ i : ι, v i := by
  simp [coordinateSum]

def standardSpace : Submodule K (ι → K) := LinearMap.ker coordinateSum

@[simp] theorem mem_standardSpace (v : ι → K) :
    v ∈ standardSpace (K := K) ↔ ∑ i : ι, v i = 0 := by
  simp [standardSpace]

def linearPolynomial : (ι → K) →ₗ[K] P :=
  (Pi.basisFun K ι).constr K (fun i => X i)

theorem linearPolynomial_apply (v : ι → K) :
    linearPolynomial v = ∑ i : ι, v i • (X i : P) := by
  simp only [linearPolynomial, Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply]

theorem linearPolynomial_injective :
    Function.Injective (linearPolynomial : (ι → K) →ₗ[K] P) :=
  (Pi.basisFun K ι).injective_constr_of_linearIndependent
    (MvPolynomial.linearIndependent_X (R := K) (σ := ι))

def standardPolynomial (q : ℕ) : standardSpace (K := K) (ι := ι) →ₗ[K] P :=
  (LinearMap.mulLeft K (PowerHarmonicWitness.sumVariables^q)).comp
    (linearPolynomial.comp (standardSpace (K := K) (ι := ι)).subtype)

@[simp] theorem standardPolynomial_apply (q : ℕ)
    (v : standardSpace (K := K) (ι := ι)) :
    standardPolynomial q v = PowerHarmonicWitness.sumVariables^q * linearPolynomial v.val := rfl

theorem sumVariables_ne_zero [Nonempty ι] :
    (PowerHarmonicWitness.sumVariables : P) ≠ 0 := by
  classical
  let b : ι := Classical.choice inferInstance
  have he : MvPolynomial.eval (fun i => if i=b then (1 : K) else 0)
      (PowerHarmonicWitness.sumVariables : P) = 1 := by
    simp [PowerHarmonicWitness.sumVariables]
  intro hz
  rw [hz, map_zero] at he
  exact zero_ne_one he

theorem standardPolynomial_injective [Nonempty ι] (q : ℕ) :
    Function.Injective (standardPolynomial (K := K) (ι := ι) q) := by
  intro v w he
  apply Subtype.ext
  apply linearPolynomial_injective
  exact mul_left_cancel₀ (pow_ne_zero q sumVariables_ne_zero) he

theorem standardPolynomial_homogeneous (q : ℕ)
    (v : standardSpace (K := K) (ι := ι)) :
    (standardPolynomial q v).IsHomogeneous (q+1) := by
  have hS : (PowerHarmonicWitness.sumVariables : P).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X K i)
  have hL : (linearPolynomial v.val).IsHomogeneous 1 := by
    rw [linearPolynomial_apply]
    exact IsHomogeneous.sum _ _ _ (fun i _ =>
      (homogeneousSubmodule ι K 1).smul_mem (v.val i) (isHomogeneous_X K i))
  simpa only [standardPolynomial_apply, Nat.one_mul, nsmul_eq_mul] using (hS.pow q).mul hL

def permuteStandard (σ : Equiv.Perm ι)
    (v : standardSpace (K := K) (ι := ι)) : standardSpace (K := K) (ι := ι) :=
  ⟨fun i => v.val (σ.symm i), by
    rw [mem_standardSpace, Equiv.sum_comp σ.symm]
    exact (mem_standardSpace v.val).mp v.property⟩

theorem rename_linearPolynomial (σ : Equiv.Perm ι) (v : ι → K) :
    rename σ (linearPolynomial v) = linearPolynomial (fun i => v (σ.symm i)) := by
  rw [linearPolynomial_apply, linearPolynomial_apply]
  simp only [map_sum, map_smul, rename_X]
  calc
    _ = ∑ i : ι, v (σ.symm (σ i)) • (X (σ i) : P) := by simp
    _ = _ := Equiv.sum_comp σ (fun i => v (σ.symm i) • (X i : P))

theorem rename_sumVariables (σ : Equiv.Perm ι) :
    rename σ (PowerHarmonicWitness.sumVariables : P) =
      PowerHarmonicWitness.sumVariables := by
  simp only [PowerHarmonicWitness.sumVariables, map_sum, rename_X]
  exact Equiv.sum_comp σ _

theorem standardPolynomial_equivariant (σ : Equiv.Perm ι) (q : ℕ)
    (v : standardSpace (K := K) (ι := ι)) :
    rename σ (standardPolynomial q v) = standardPolynomial q (permuteStandard σ v) := by
  simp only [standardPolynomial_apply, map_mul, map_pow,
    rename_sumVariables, rename_linearPolynomial, permuteStandard]

theorem standardPolynomial_eq_sum_witness (q : ℕ)
    (v : standardSpace (K := K) (ι := ι)) (b : ι) :
    standardPolynomial q v = ∑ i : ι,
      v.val i • PowerHarmonicWitness.harmonicWitness i b q := by
  rw [standardPolynomial_apply, linearPolynomial_apply, Finset.mul_sum]
  have hv := (mem_standardSpace v.val).mp v.property
  simp only [PowerHarmonicWitness.harmonicWitness, mul_sub, smul_sub,
    Finset.sum_sub_distrib, mul_smul_comm, ← Finset.sum_smul, hv,
    zero_smul, sub_zero]

theorem standardPolynomial_annihilates_original [Nonempty ι]
    (α : K) (q : ℕ)
    (hres : (Fintype.card ι : K) + α*(q+1 : ℕ) = 0)
    (v : standardSpace (K := K) (ι := ι)) (k : ℕ) (hk : 0 < k) (p : P) :
    PowerFischerPairing.fischer
      (PowerOperators.original (fun _ => (1 : K)) α k p) (standardPolynomial q v) = 0 := by
  let b : ι := Classical.choice inferInstance
  rw [standardPolynomial_eq_sum_witness q v b, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, PowerFischerPairing.resonant_witness_annihilates_original
    α i b q hres k hk, smul_zero]

def standardQuotientDualMap [Nonempty ι]
    (α : K) (q : ℕ)
    (hres : (Fintype.card ι : K) + α*(q+1 : ℕ) = 0) :
    standardSpace (K := K) (ι := ι) →ₗ[K]
      Module.Dual K (P ⧸ PowerOperators.originalTailHit (fun _ => (1 : K)) α 1) where
  toFun v :=
    (PowerOperators.originalTailHit (fun _ => (1 : K)) α 1).liftQ
      (PowerFischerPairing.fischer.flip (standardPolynomial q v)) (by
        apply Submodule.span_le.mpr
        rintro _ ⟨k, hk, p, rfl⟩
        exact standardPolynomial_annihilates_original α q hres v k hk p)
  map_add' v w := by
    apply LinearMap.ext
    intro z
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change PowerFischerPairing.fischer p (standardPolynomial q (v+w)) = _
    simp only [map_add, LinearMap.add_apply, Submodule.liftQ_apply, LinearMap.flip_apply]
  map_smul' a v := by
    apply LinearMap.ext
    intro z
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change PowerFischerPairing.fischer p (standardPolynomial q (a • v)) = _
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply,
      Submodule.liftQ_apply, LinearMap.flip_apply]

@[simp] theorem standardQuotientDualMap_mkQ [Nonempty ι]
    (α : K) (q : ℕ)
    (hres : (Fintype.card ι : K) + α*(q+1 : ℕ) = 0)
    (v : standardSpace (K := K) (ι := ι)) (p : P) :
    standardQuotientDualMap α q hres v
      ((PowerOperators.originalTailHit (fun _ => (1 : K)) α 1).mkQ p) =
      PowerFischerPairing.fischer p (standardPolynomial q v) := rfl

theorem standardQuotientDualMap_injective [Nonempty ι] [CharZero K]
    (α : K) (q : ℕ)
    (hres : (Fintype.card ι : K) + α*(q+1 : ℕ) = 0) :
    Function.Injective (standardQuotientDualMap (ι := ι) α q hres) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply (standardPolynomial_injective q)
  rw [map_zero]
  apply PowerFischerPairing.fischer_right_nondegenerate
  intro p
  have h := LinearMap.congr_fun hv
    ((PowerOperators.originalTailHit (fun _ => (1 : K)) α 1).mkQ p)
  exact h

/-- Restriction to the actual degree `q+1` quotient piece. -/
def standardDegreeDualMap [Nonempty ι]
    (α : K) (q : ℕ)
    (hres : (Fintype.card ι : K) + α*(q+1 : ℕ) = 0) :
    standardSpace (K := K) (ι := ι) →ₗ[K]
      Module.Dual K (PowerOperators.originalTailQuotientDegree
        (fun _ : ι => (1 : K)) α 1 (q+1)) where
  toFun v := (standardQuotientDualMap α q hres v).comp
    (PowerOperators.originalTailQuotientDegree
      (fun _ : ι => (1 : K)) α 1 (q+1)).subtype
  map_add' v w := by
    simp only [map_add, LinearMap.add_comp]
  map_smul' a v := by
    simp only [map_smul, LinearMap.smul_comp, RingHom.id_apply]

theorem standardDegreeDualMap_injective [Nonempty ι] [CharZero K]
    (α : K) (q : ℕ)
    (hres : (Fintype.card ι : K) + α*(q+1 : ℕ) = 0) :
    Function.Injective (standardDegreeDualMap (ι := ι) α q hres) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply standardPolynomial_injective q
  rw [map_zero]
  apply PowerFischerPairing.fischer_right_nondegenerate
  intro p
  let x : PowerOperators.originalTailQuotientDegree
      (fun _ : ι => (1 : K)) α 1 (q+1) :=
    ⟨(PowerOperators.originalTailHit (fun _ : ι => (1 : K)) α 1).mkQ
      (homogeneousComponent (q+1) p),
      ⟨_, homogeneousComponent_mem _ _, rfl⟩⟩
  have he := LinearMap.congr_fun hv x
  change PowerFischerPairing.fischer (homogeneousComponent (q+1) p)
    (standardPolynomial q v) = 0 at he
  rwa [PowerFischerPairing.fischer_homogeneousComponent_left p _ (q+1)
    (standardPolynomial_homogeneous q v)] at he

/-- The induced functionals have the contragredient permutation action on
the actual quotient, checked on its surjective polynomial presentation. -/
theorem standardQuotientDualMap_permutation [Nonempty ι]
    (α : K) (q : ℕ)
    (hres : (Fintype.card ι : K) + α*(q+1 : ℕ) = 0)
    (σ : Equiv.Perm ι) (v : standardSpace (K := K) (ι := ι)) (p : P) :
    standardQuotientDualMap α q hres (permuteStandard σ v)
      ((PowerOperators.originalTailHit (fun _ => (1 : K)) α 1).mkQ p) =
    standardQuotientDualMap α q hres v
      ((PowerOperators.originalTailHit (fun _ => (1 : K)) α 1).mkQ (rename σ.symm p)) := by
  rw [standardQuotientDualMap_mkQ, standardQuotientDualMap_mkQ,
    ← standardPolynomial_equivariant, PowerFischerPairing.fischer_rename_right]

end PaperVerification.PowerStandardHarmonics
