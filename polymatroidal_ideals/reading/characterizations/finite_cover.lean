import Mathlib.Algebra.BigOperators.Field
import Characterizations.PatternProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! # A kernel-checked probabilistic covering bound for finite tests -/

noncomputable section
namespace Characterizations
open Classical Finset
variable {X I : Type*} [Fintype X] [Fintype I]

theorem finiteFraction_not [Nonempty X] (P : X → Prop) :
    finiteFraction (fun x => ¬P x) = 1 - finiteFraction P := by
  classical
  have hle := Fintype.card_subtype_le P
  have hpos : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  unfold finiteFraction
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  rw [Nat.cast_sub hle]
  field_simp

theorem finiteFraction_exists_le_sum (R : I → X → Prop) :
    finiteFraction (fun x => ∃ i,R i x) ≤ ∑ i, finiteFraction (R i) := by
  classical
  let f : {x // ∃ i,R i x} → Σ i : I, {x // R i x} :=
    fun x => ⟨x.property.choose,⟨x.val,x.property.choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : Σ i : I, {x // R i x} => z.2.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sigma] at hc
  unfold finiteFraction
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc

def allTrialEquiv (M : ℕ) (P : X → Prop) :
    {f : Fin M → X // ∀ j,P (f j)} ≃ (Fin M → {x // P x}) where
  toFun f j := ⟨f.val j,f.property j⟩
  invFun f := ⟨fun j => (f j).val,fun j => (f j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finiteFraction_all_trials (M : ℕ) (P : X → Prop) :
    finiteFraction (fun f : Fin M → X => ∀ j,P (f j)) = (finiteFraction P)^M := by
  unfold finiteFraction
  rw [Nat.card_congr (allTrialEquiv M P),Nat.card_fun,Nat.card_fun]
  simp only [Nat.card_fin,Nat.cast_pow,div_pow]

theorem finiteFraction_nonneg (P : X → Prop) : 0 ≤ finiteFraction P := by
  unfold finiteFraction
  positivity

theorem exists_outside_of_fraction_lt_one [Nonempty X] (P : X → Prop)
    (h : finiteFraction P < 1) : ∃ x, ¬P x := by
  by_contra hn
  have hP : ∀ x,P x := by simpa using hn
  have he : finiteFraction P = 1 := by
    rw [finiteFraction_congr (fun x => iff_true_intro (hP x)),finiteFraction_true]
  linarith

/-- Independent draws miss at most the sum of the exact individual missing
probabilities. This is a finite counting proof of the union bound. -/
theorem independent_miss_fraction_bound [Nonempty X] (R : I → X → Prop)
    (p : ℝ) (hp : 0 ≤ p) (hR : ∀ i, finiteFraction (R i) = p) (M : ℕ) :
    finiteFraction (fun f : Fin M → X => ∃ i,∀ j,¬R i (f j)) ≤
      (Fintype.card I : ℝ) * Real.exp (-p * M) := by
  have hsum := finiteFraction_exists_le_sum (fun i (f : Fin M → X) => ∀ j,¬R i (f j))
  have hsingle (i : I) : finiteFraction (fun f : Fin M → X => ∀ j,¬R i (f j)) = (1-p)^M := by
    rw [finiteFraction_all_trials M (fun x => ¬R i x),finiteFraction_not (R i),hR i]
  simp only [hsingle,sum_const,card_univ,nsmul_eq_mul] at hsum
  apply hsum.trans
  by_cases hI : Nonempty I
  · letI := hI
    have hple : p ≤ 1 := by
      obtain ⟨i⟩ := hI
      simpa [hR i] using finiteFraction_le_one (R i)
    have hexp : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1-p) hexp M
    have he : Real.exp (-p)^M = Real.exp (-p * M) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he] at hpow
    exact mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
  · haveI : IsEmpty I := not_nonempty_iff.mp hI
    simp

/-- A finite family meeting all tests, with the exact logarithmic size bound. -/
theorem finite_probabilistic_cover [Nonempty X] [Nonempty I]
    (R : I → X → Prop) (p : ℝ) (hp : 0 < p)
    (hR : ∀ i, finiteFraction (R i) = p) :
    ∃ F : Finset X, F.card ≤ ⌈p⁻¹ * (Real.log (Fintype.card I) + 1)⌉₊ ∧
      ∀ i, ∃ x ∈ F,R i x := by
  classical
  let M : ℕ := ⌈p⁻¹ * (Real.log (Fintype.card I) + 1)⌉₊
  have hM : p⁻¹ * (Real.log (Fintype.card I) + 1) ≤ (M : ℝ) := Nat.le_ceil _
  have hQ : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpM : Real.log (Fintype.card I) + 1 ≤ p * M := by
    have hh := mul_le_mul_of_nonneg_left hM hp.le
    simpa [← mul_assoc,mul_inv_cancel₀ hp.ne'] using hh
  have hbound : (Fintype.card I : ℝ) * Real.exp (-p*M) < 1 := by
    calc
      _ = Real.exp (Real.log (Fintype.card I) - p*M) := by
        rw [Real.exp_sub,Real.exp_log hQ]
        simp [Real.exp_neg,div_eq_mul_inv]
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ < 1 := by simpa using (Real.exp_lt_exp.mpr (show (-1:ℝ)<0 by norm_num))
  obtain ⟨f,hf⟩ := exists_outside_of_fraction_lt_one
    (fun f : Fin M → X => ∃ i,∀ j,¬R i (f j))
    ((independent_miss_fraction_bound R p hp.le hR M).trans_lt hbound)
  refine ⟨univ.image f,?_,?_⟩
  · exact (card_image_le).trans (by simp [M])
  · intro i
    have hi : ∃ j,R i (f j) := by
      by_contra hn
      exact hf ⟨i,by simpa using hn⟩
    obtain ⟨j,hj⟩ := hi
    exact ⟨f j,mem_image.mpr ⟨j,mem_univ _,rfl⟩,hj⟩

end Characterizations
