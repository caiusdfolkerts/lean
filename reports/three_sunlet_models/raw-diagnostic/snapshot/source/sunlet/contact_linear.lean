module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Module
public import Lean.Elab.Tactic.Omega

/-! Linear algebra for the sparse contact calculation. -/

@[expose] public section
noncomputable section

namespace Sunlet.ContactLinear

variable {K Ω V : Type*} [Field K]

def evaluation (o : Ω) : (Ω → K) →ₗ[K] K where
  toFun F := F o
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def zeroAt (o : Ω) : Submodule K (Ω → K) := (evaluation (K := K) o).ker

@[simp] theorem mem_zeroAt (o : Ω) (F : Ω → K) : F ∈ zeroAt (K := K) o ↔ F o = 0 := Iff.rfl

theorem evaluation_surjective (o : Ω) : Function.Surjective (evaluation (K := K) o) :=
  fun a => ⟨fun _ => a, rfl⟩

theorem zeroAt_finrank_add_one [Fintype Ω] (o : Ω) :
    Module.finrank K (zeroAt (K := K) o) + 1 = Fintype.card Ω := by
  have h := (evaluation (K := K) o).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (evaluation_surjective (K := K) o)] at h
  change Module.finrank K (evaluation (K := K) o).ker + 1 = Fintype.card Ω
  have hh : 1 + Module.finrank K (evaluation (K := K) o).ker = Fintype.card Ω := by
    simpa only [finrank_top, Module.finrank_self, Module.finrank_pi, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using h
  omega

theorem exists_outside_sum [Fintype Ω] (o : Ω) (W₁ W₂ : Submodule K (Ω → K))
    (hsmall : Module.finrank K W₁ + Module.finrank K W₂ < Fintype.card Ω - 1) :
    ∃ H : Ω → K, H o = 0 ∧ H ∉ W₁ ⊔ W₂ := by
  have hnot : ¬zeroAt (K := K) o ≤ W₁ ⊔ W₂ := by
    intro hle
    have hdim := Submodule.finrank_mono hle
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
    have hzero := zeroAt_finrank_add_one (K := K) o
    omega
  change ¬∀ H, H ∈ zeroAt (K := K) o → H ∈ W₁ ⊔ W₂ at hnot
  obtain ⟨H, hH⟩ := not_forall.mp hnot
  obtain ⟨hHo, hH⟩ := not_imp.mp hH
  exact ⟨H, hHo, hH⟩

variable [AddCommGroup V] [Module K V]

def reflectionOperator (e : V) (μ : V →ₗ[K] K) (lam : K) : V →ₗ[K] V :=
  lam • LinearMap.id - μ.smulRight e

@[simp] theorem reflectionOperator_apply (e : V) (μ : V →ₗ[K] K) (lam : K) (x : V) :
    reflectionOperator e μ lam x = lam • x - μ x • e := rfl

theorem reflectionOperator_square (e : V) (μ : V →ₗ[K] K) (lam : K)
    (hμ : μ e = 2 * lam) (x : V) :
    reflectionOperator e μ lam (reflectionOperator e μ lam x) = lam ^ 2 • x := by
  simp only [reflectionOperator_apply, map_sub, map_smul, hμ, smul_eq_mul]
  module

/-- The rank-one correction in (6) is invertible whenever its leading scalar
is nonzero; its square is the square scalar operator. -/
theorem reflectionOperator_surjective (e : V) (μ : V →ₗ[K] K) (lam : K)
    (hμ : μ e = 2 * lam) (hlam : lam ≠ 0) : Function.Surjective (reflectionOperator e μ lam) := by
  intro y
  refine ⟨(lam ^ 2)⁻¹ • reflectionOperator e μ lam y, ?_⟩
  rw [map_smul, reflectionOperator_square e μ lam hμ, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hlam), one_smul]

end Sunlet.ContactLinear
