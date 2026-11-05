import bier.forster.gram_determinant

/-! # Equal leverage scores at the determinant minimum

A zero-sum logarithmic variation changes one weight and scales all weights
equally.  The matrix determinant lemma gives its derivative without invoking
an unproved matrix-calculus formula.
-/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix

variable {k n : ℕ}

theorem det_add_smul_outer (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.det ≠ 0) (u : Fin k → ℝ) (t : ℝ) :
    (A + t • vecMulVec u u).det =
      A.det * (1 + t * (u ⬝ᵥ (A⁻¹ *ᵥ u))) := by
  rw [← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hA)]
  congr 1
  rw [Matrix.det_unique, Matrix.mul_assoc]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct, Matrix.mulVec]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem weightedGram_smul (U : Matrix (Fin k) (Fin n) ℝ) (w : Fin n → ℝ) (s : ℝ) :
    weightedGram U (s • w) = s • weightedGram U w := by
  ext a b
  simp only [weightedGram_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weightedGram_update (U : Matrix (Fin k) (Fin n) ℝ)
    (w : Fin n → ℝ) (i : Fin n) (a : ℝ) :
    weightedGram U (Function.update w i a) =
      weightedGram U w + (a - w i) • vecMulVec (fun j => U j i) (fun j => U j i) := by
  ext r c
  simp only [weightedGram_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply]
  calc
    (∑ j, Function.update w i a j * U r j * U c j) =
        ∑ j, (w j * U r j * U c j + if j = i then (a - w i) * (U r i * U c i) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases he : j = i
      · subst j; simp; ring
      · simp [Function.update_of_ne he, he]
    _ = _ := by simp [Finset.sum_add_distrib]

def logarithmicDirection (i : Fin n) : zeroSumSpace (Fin n) :=
  ⟨fun j => (if j = i then 1 else 0) - 1 / (n : ℝ), by
    rw [mem_zeroSumSpace]
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := i.isLt; omega)
    simp [Finset.sum_sub_distrib, hn]⟩

theorem logarithmic_weight_curve (x : zeroSumSpace (Fin n)) (i : Fin n) (t : ℝ) :
    (fun j => Real.exp ((x + t • logarithmicDirection i).val j)) =
      Real.exp (-(t / n)) • Function.update (fun j => Real.exp (x.val j)) i
        (Real.exp t * Real.exp (x.val i)) := by
  funext j
  change Real.exp (x.val j + t * ((if j = i then 1 else 0) - 1 / (n : ℝ))) = _
  by_cases hji : j = i
  · subst j
    simp only [ite_true, Function.update_self, Pi.smul_apply, smul_eq_mul]
    rw [show x.val i + t * (1 - 1 / (n : ℝ)) = -(t / n) + (t + x.val i) by ring,
      Real.exp_add, Real.exp_add]
  · simp only [hji, ite_false, Function.update_of_ne hji, Pi.smul_apply, smul_eq_mul]
    rw [show x.val j + t * (0 - 1 / (n : ℝ)) = -(t / n) + x.val j by ring,
      Real.exp_add]

def leverage (U : Matrix (Fin k) (Fin n) ℝ) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  w i * ((fun a => U a i) ⬝ᵥ ((weightedGram U w)⁻¹ *ᵥ (fun a => U a i)))

theorem logarithmic_det_curve (U : Matrix (Fin k) (Fin n) ℝ)
    (x : zeroSumSpace (Fin n)) (hD : (weightedGram U (fun j => Real.exp (x.val j))).det ≠ 0)
    (i : Fin n) (t : ℝ) :
    (weightedGram U (fun j => Real.exp ((x + t • logarithmicDirection i).val j))).det =
      Real.exp (-(t / n)) ^ k *
        (weightedGram U (fun j => Real.exp (x.val j))).det *
          (1 + (Real.exp t - 1) * leverage U (fun j => Real.exp (x.val j)) i) := by
  rw [logarithmic_weight_curve, weightedGram_smul, Matrix.det_smul, Fintype.card_fin,
    weightedGram_update, det_add_smul_outer _ hD]
  simp only [leverage]
  ring

theorem equal_leverage_of_minimum (U : Matrix (Fin k) (Fin n) ℝ)
    (x : zeroSumSpace (Fin n)) (hD : (weightedGram U (fun j => Real.exp (x.val j))).det ≠ 0)
    (hmin : ∀ y : zeroSumSpace (Fin n),
      (weightedGram U (fun j => Real.exp (x.val j))).det ≤
        (weightedGram U (fun j => Real.exp (y.val j))).det)
    (i : Fin n) : leverage U (fun j => Real.exp (x.val j)) i = (k : ℝ) / n := by
  let D := (weightedGram U (fun j => Real.exp (x.val j))).det
  let a := leverage U (fun j => Real.exp (x.val j)) i
  let f : ℝ → ℝ := fun t => Real.exp (-(t / n)) ^ k * D * (1 + (Real.exp t - 1) * a)
  have hloc : IsLocalMin f 0 := by
    apply IsMinOn.isLocalMin (s := Set.univ)
    · intro t ht
      have hh := hmin (x + t • logarithmicDirection i)
      rw [logarithmic_det_curve U x hD i t] at hh
      simpa [f, D, a] using hh
    · exact Filter.univ_mem
  have hd : HasDerivAt f (D * (a - (k : ℝ) / n)) 0 := by
    have he : HasDerivAt (fun t : ℝ => Real.exp (-(t / n))) (-(1 / (n : ℝ))) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).div_const (n : ℝ)).neg.exp using 1 <;> simp
    have he2 : HasDerivAt (fun t : ℝ => 1 + (Real.exp t - 1) * a) a 0 := by
      simpa using (((Real.hasDerivAt_exp (0 : ℝ)).sub_const 1).mul_const a).const_add 1
    convert ((he.pow k).mul_const D).mul he2 using 1 <;> simp [f] <;> ring
  have hz := hloc.hasDerivAt_eq_zero hd
  have hz' : a - (k : ℝ) / n = 0 := (mul_eq_zero.mp hz).resolve_left hD
  exact sub_eq_zero.mp hz'

theorem exists_equal_leverage (U : Matrix (Fin k) (Fin n) ℝ)
    (hk : 0 < k) (hkn : k < n)
    (hu : ∀ S : KSubset (Fin n) k, 0 < minorSquare U S) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ (weightedGram U w).PosDef ∧
      ∀ i, leverage U w i = (k : ℝ) / n := by
  obtain ⟨x, hx⟩ := exists_weightedGram_minimum U hk hkn hu
  have hD := weightedGram_exp_posDef U hkn.le hu x
  exact ⟨fun j => Real.exp (x.val j), fun j => Real.exp_pos _, hD,
    equal_leverage_of_minimum U x hD.det_pos.ne' hx⟩

end Bier.Forster
