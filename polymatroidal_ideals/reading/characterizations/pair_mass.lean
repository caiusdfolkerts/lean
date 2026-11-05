import Characterizations.PatternProbability

/-! # A pointed triple injects into any prescribed final pair event -/

noncomputable section
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triple_to_pair_card_le {i q j k : V}
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j)
    (hki : k ≠ i) (hkq : k ≠ q) (hkj : k ≠ j) :
    Nat.card {o : VariableOrder V // FinalTriple o i q j} ≤
      Nat.card {o : VariableOrder V // FinalPair o i j} := by
  let σ : Equiv.Perm V := (Equiv.swap q k).trans (Equiv.swap i q)
  have hσi : σ i = q := by simp [σ,Equiv.swap_apply_def,hiq,hiq.symm,hki.symm]
  have hσq : σ q = k := by simp [σ,Equiv.swap_apply_def,hki,hkq]
  have hσk : σ k = i := by simp [σ,Equiv.swap_apply_def,hkq.symm]
  have hσj : σ j = j := by simp [σ,Equiv.swap_apply_def,hij.symm,hqj.symm,hkj.symm]
  have hσx (x : V) (hxi : x ≠ i) (hxq : x ≠ q) (hxk : x ≠ k) : σ x = x := by
    simp [σ,Equiv.swap_apply_def,hxi,hxq,hxk,Ne.symm hxi,Ne.symm hxq,Ne.symm hxk]
  let f (o : VariableOrder V) : VariableOrder V := if o q < o i then o else σ.trans o
  have hf (o : VariableOrder V) (ho : FinalTriple o i q j) : FinalPair (f o) i j := by
    by_cases hqi : o q < o i
    · simp only [f,if_pos hqi]
      refine ⟨ho.1,?_⟩
      intro x hxi hxj
      by_cases hxq : x = q
      · simpa [hxq] using hqi
      · exact (ho.2.2 x hxi hxq hxj).1
    · have hiqO : o i < o q := lt_of_le_of_ne (le_of_not_gt hqi)
        (fun he => hiq (o.injective he))
      simp only [f,if_neg hqi]
      refine ⟨?_,?_⟩
      · simpa only [Equiv.trans_apply,hσi,hσj] using ho.2.1
      · intro x hxi hxj
        by_cases hxq : x = q
        · subst x
          simpa only [Equiv.trans_apply,hσq,hσi] using (ho.2.2 k hki hkq hkj).2
        by_cases hxk : x = k
        · subst x
          simpa only [Equiv.trans_apply,hσk,hσi] using hiqO
        · simpa only [Equiv.trans_apply,hσi,hσx x hxi hxq hxk] using (ho.2.2 x hxi hxq hxj).2
  have hsignal (o : VariableOrder V) (ho : FinalTriple o i q j) :
      (f o) q < (f o) k ↔ ¬ o q < o i := by
    by_cases hqi : o q < o i
    · simp only [f,if_pos hqi,hqi,not_true_eq_false,iff_false]
      exact not_lt_of_gt (ho.2.2 k hki hkq hkj).2
    · simp only [f,if_neg hqi,Equiv.trans_apply,hσq,hσk,hqi,not_false_eq_true,iff_true]
      exact (ho.2.2 k hki hkq hkj).1
  let g : {o : VariableOrder V // FinalTriple o i q j} → {o : VariableOrder V // FinalPair o i j} :=
    fun o => ⟨f o.val,hf o.val o.property⟩
  apply Nat.card_le_card_of_injective g
  intro o o' he
  have heq : f o.val = f o'.val := congrArg Subtype.val he
  have hcond : (o.val q < o.val i) ↔ (o'.val q < o'.val i) := by
    have hs : (¬o.val q < o.val i) ↔ ¬o'.val q < o'.val i := by
      rw [← hsignal o.val o.property,← hsignal o'.val o'.property,heq]
    tauto
  apply Subtype.ext
  by_cases h : o.val q < o.val i
  · simpa only [f,if_pos h,if_pos (hcond.mp h)] using heq
  · have h' : ¬o'.val q < o'.val i := fun h' => h (hcond.mpr h')
    simp only [f,if_neg h,if_neg h'] at heq
    apply Equiv.ext
    intro x
    have hx := congrArg (fun e : VariableOrder V => e (σ.symm x)) heq
    simpa using hx

theorem finalPair_probability_lower_bound (hcard : 4 ≤ Fintype.card V) {i j : V} (hij : i ≠ j) :
    1 / (Fintype.card V * (Fintype.card V-1).choose 2 : ℕ) ≤
      finiteFraction (fun o : VariableOrder V => FinalPair o i j) := by
  have hpaircard : (pairCap i j).card = Fintype.card V-2 := by
    rw [pairCap,card_sdiff_of_subset (subset_univ _)]
    simp [hij]
  obtain ⟨q,hq⟩ : (pairCap i j).Nonempty := card_pos.mp (by omega)
  obtain ⟨hqi,hqj⟩ := (mem_pairCap _ _ _).mp hq
  have hcapcard : (tripleCap i q j).card = Fintype.card V-3 := by
    rw [tripleCap,card_sdiff_of_subset (subset_univ _)]
    simp [hqi.symm,hij,hqj]
  obtain ⟨k,hk⟩ : (tripleCap i q j).Nonempty := card_pos.mp (by omega)
  obtain ⟨hki,hkq,hkj⟩ := (mem_tripleCap _ _ _ _).mp hk
  let P : PointedTriple V := ⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hqi.symm]⟩⟩
  have hprob : finiteFraction (fun o : VariableOrder V => FinalTriple o i q j) =
      1 / (Fintype.card V * (Fintype.card V-1).choose 2 : ℕ) := by
    rw [← pointedTriple_probability (by omega) P]
    exact finiteFraction_congr (fun o => (coversPoint_pair_iff hqi.symm hij hqj).symm)
  rw [←hprob]
  unfold finiteFraction
  exact div_le_div_of_nonneg_right (by exact_mod_cast triple_to_pair_card_le hqi.symm hij hqj hki hkq hkj)
    (Nat.cast_nonneg _)

end Characterizations
