module
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option autoImplicit false

/-!
# The cyclic linear algebra in the full-dimensional projection obstruction

This file proves the final finite-dimensional contradiction in Proposition 4.2.
The hypotheses are explicit matrix identities.  The construction of those
identities from mixed-area measures is a separate geometric theorem.
-/
namespace VolumeVerification.CycleObstruction
open scoped BigOperators Matrix

section Cycle
variable {n : ℕ} [NeZero n]

theorem zero_propagates_around_cycle (w : Fin n → ℝ)
    (hstep : ∀ i, w i = 0 → w (finRotate n i) = 0)
    (i : Fin n) (hi : w i = 0) : w = 0 := by
  have hiter : ∀ k : ℕ, w ((finRotate n)^[k] i) = 0 := by
    intro k
    induction k with
    | zero => simpa using hi
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply]
        exact hstep _ ih
  funext j
  have hj := hiter ((j - i).val)
  rw [← finCycle_eq_finRotate_iterate (k := j - i)] at hj
  have hindex : finCycle (j - i) i = j := by
    change i + (j - i) = j
    abel
  simpa only [hindex, Pi.zero_apply] using hj

theorem finrank_le_one_of_zero_propagation
    (K : Submodule ℝ (Fin n → ℝ))
    (hstep : ∀ w ∈ K, ∀ i, w i = 0 → w (finRotate n i) = 0) :
    Module.finrank ℝ K ≤ 1 := by
  let ev : K →ₗ[ℝ] ℝ := (LinearMap.proj (0 : Fin n)).comp K.subtype
  have hinj : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro w hw
    have hw0 : (w : Fin n → ℝ) 0 = 0 := hw
    have hz := zero_propagates_around_cycle (w : Fin n → ℝ)
      (hstep _ w.property) 0 hw0
    exact Subtype.ext hz
  rw [← LinearMap.finrank_range_of_inj hinj]
  simpa using ev.range.finrank_le

/-- Column i is alpha_i e_i + beta_i e_(i+1). -/
def cycleIncidence (alpha beta : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then alpha j else 0) +
    (if i = finRotate n j then beta j else 0)

theorem transpose_cycleIncidence_mulVec (alpha beta w : Fin n → ℝ) (i : Fin n) :
    ((cycleIncidence alpha beta)ᵀ *ᵥ w) i =
      alpha i * w i + beta i * w (finRotate n i) := by
  simp [Matrix.mulVec, dotProduct, cycleIncidence, Matrix.transpose_apply,
    add_mul, ite_mul, Finset.sum_add_distrib]

theorem weighted_cycle_zero_propagation (alpha beta w : Fin n → ℝ)
    (hbeta : ∀ i, beta i ≠ 0)
    (hrel : ∀ i, alpha i * w i + beta i * w (finRotate n i) = 0) :
    ∀ i, w i = 0 → w (finRotate n i) = 0 := by
  intro i hi
  have h := hrel i
  rw [hi, mul_zero, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left (hbeta i)

theorem cycle_kernel_finrank_le_one (alpha beta : Fin n → ℝ)
    (hbeta : ∀ i, beta i ≠ 0) :
    Module.finrank ℝ (cycleIncidence alpha beta)ᵀ.mulVecLin.ker ≤ 1 := by
  apply finrank_le_one_of_zero_propagation
  intro w hw
  have hrel : ∀ i, alpha i * w i + beta i * w (finRotate n i) = 0 := by
    intro i
    have hi := congrFun hw i
    simpa only [Matrix.mulVecLin_apply, transpose_cycleIncidence_mulVec,
      Pi.zero_apply] using hi
  exact weighted_cycle_zero_propagation alpha beta w hbeta hrel

theorem odd_weighted_cycle_zero (alpha beta w : Fin n → ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : ∀ i, 0 < beta i)
    (hodd : Odd n)
    (hrel : ∀ i, alpha i * w i + beta i * w (finRotate n i) = 0) :
    w = 0 := by
  have hmul : ∀ i, alpha i * w i = (-beta i) * w (finRotate n i) := by
    intro i
    linarith [hrel i]
  have hprod := congrArg (fun f : Fin n → ℝ => ∏ i, f i) (funext hmul)
  have hrotate : (∏ i, w (finRotate n i)) = ∏ i, w i :=
    Fintype.prod_equiv (finRotate n) _ _ (fun _ => rfl)
  simp only [Finset.prod_mul_distrib, Finset.prod_neg, Finset.card_univ,
    Fintype.card_fin, hodd.neg_one_pow, hrotate] at hprod
  have hpa : 0 < ∏ i, alpha i := Finset.prod_pos fun i _ => halpha i
  have hpb : 0 < ∏ i, beta i := Finset.prod_pos fun i _ => hbeta i
  have hpw : (∏ i, w i) = 0 := by
    have he : ((∏ i, alpha i) + ∏ i, beta i) * (∏ i, w i) = 0 := by
      nlinarith [hprod]
    exact (mul_eq_zero.mp he).resolve_left (add_pos hpa hpb).ne'
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hpw
  exact zero_propagates_around_cycle w
    (weighted_cycle_zero_propagation alpha beta w (fun i => (hbeta i).ne') hrel) i hi

theorem odd_cycle_kernel_eq_bot (alpha beta : Fin n → ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : ∀ i, 0 < beta i) (hodd : Odd n) :
    (cycleIncidence alpha beta)ᵀ.mulVecLin.ker = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  apply odd_weighted_cycle_zero alpha beta w halpha hbeta hodd
  intro i
  have hi := congrFun hw i
  simpa only [Matrix.mulVecLin_apply, transpose_cycleIncidence_mulVec,
    Pi.zero_apply] using hi

theorem cycle_rank_add_one_ge (alpha beta : Fin n → ℝ)
    (hbeta : ∀ i, beta i ≠ 0) :
    n ≤ (cycleIncidence alpha beta).rank + 1 := by
  have hk := cycle_kernel_finrank_le_one alpha beta hbeta
  have hr := (cycleIncidence alpha beta)ᵀ.mulVecLin.finrank_range_add_finrank_ker
  change (cycleIncidence alpha beta)ᵀ.rank +
    Module.finrank ℝ (cycleIncidence alpha beta)ᵀ.mulVecLin.ker =
      Module.finrank ℝ (Fin n → ℝ) at hr
  rw [Matrix.rank_transpose] at hr
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr
  omega

theorem odd_cycle_rank (alpha beta : Fin n → ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : ∀ i, 0 < beta i) (hodd : Odd n) :
    (cycleIncidence alpha beta).rank = n := by
  have hr := (cycleIncidence alpha beta)ᵀ.mulVecLin.finrank_range_add_finrank_ker
  change (cycleIncidence alpha beta)ᵀ.rank +
    Module.finrank ℝ (cycleIncidence alpha beta)ᵀ.mulVecLin.ker =
      Module.finrank ℝ (Fin n → ℝ) at hr
  rw [odd_cycle_kernel_eq_bot alpha beta halpha hbeta hodd] at hr
  simpa only [finrank_bot, add_zero, Matrix.rank_transpose,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hr

end Cycle

section RankBounds
variable {n : ℕ} [NeZero n]

theorem transpose_kernel_finrank_eq (Z : Matrix (Fin n) (Fin n) ℝ) :
    Module.finrank ℝ Zᵀ.mulVecLin.ker = Module.finrank ℝ Z.mulVecLin.ker := by
  have h1 := Z.mulVecLin.finrank_range_add_finrank_ker
  have h2 := Zᵀ.mulVecLin.finrank_range_add_finrank_ker
  change Z.rank + Module.finrank ℝ Z.mulVecLin.ker =
    Module.finrank ℝ (Fin n → ℝ) at h1
  change Zᵀ.rank + Module.finrank ℝ Zᵀ.mulVecLin.ker =
    Module.finrank ℝ (Fin n → ℝ) at h2
  rw [Matrix.rank_transpose] at h2
  omega

theorem rank_le_kernel_finrank_of_mul_zero
    (Z M : Matrix (Fin n) (Fin n) ℝ) (hZM : Z * M = 0) :
    M.rank ≤ Module.finrank ℝ Z.mulVecLin.ker := by
  have hsub : M.mulVecLin.range ≤ Z.mulVecLin.ker := by
    rintro x ⟨y,rfl⟩
    change Z *ᵥ (M *ᵥ y) = 0
    rw [Matrix.mulVec_mulVec, hZM, Matrix.zero_mulVec]
  exact Submodule.finrank_mono hsub

/-- The final contradiction of Proposition 4.2, for every n >= 5.
The geometric construction must supply the displayed identities. -/
theorem no_cycle_factorization (hn : 5 ≤ n)
    (W : Matrix (Fin (n-3)) (Fin n) ℝ) (hW : W.rank = n-3)
    (Z : Matrix (Fin n) (Fin n) ℝ)
    (hrelations : ∀ w, Zᵀ *ᵥ w = 0 →
      ∀ i, w i = 0 → w (finRotate n i) = 0)
    (alpha beta : Fin n → ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : ∀ i, 0 < beta i)
    (L : Matrix (Fin (n-3)) (Fin n) ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hZM : Z * M = 0)
    (hfactor : W * cycleIncidence alpha beta = L * M) :
    False := by
  have hkerT : Module.finrank ℝ Zᵀ.mulVecLin.ker ≤ 1 :=
    finrank_le_one_of_zero_propagation _ (fun w hw => hrelations w hw)
  have hker : Module.finrank ℝ Z.mulVecLin.ker ≤ 1 := by
    rwa [transpose_kernel_finrank_eq] at hkerT
  have hM : M.rank ≤ 1 :=
    (rank_le_kernel_finrank_of_mul_zero Z M hZM).trans hker
  have hupper : (W * cycleIncidence alpha beta).rank ≤ 1 := by
    rw [hfactor]
    exact (Matrix.rank_mul_le_right L M).trans hM
  have hge := Matrix.rank_mul_ge W (cycleIncidence alpha beta)
  rw [hW, Fintype.card_fin] at hge
  by_cases hfive : n = 5
  · have hodd : Odd n := by rw [hfive]; exact ⟨2, rfl⟩
    rw [odd_cycle_rank alpha beta halpha hbeta hodd] at hge
    omega
  · have hD := cycle_rank_add_one_ge alpha beta (fun i => (hbeta i).ne')
    omega

end RankBounds
end VolumeVerification.CycleObstruction

