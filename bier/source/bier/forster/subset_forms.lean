import bier.forster.exponential_minimum
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Pi

/-! # Balanced subset-sum forms on the zero-sum hyperplane -/

noncomputable section

namespace Bier.Forster

open Classical Finset

variable (X : Type*) [Fintype X]

abbrev KSubset (k : ℕ) := ↥((univ : Finset X).powersetCard k)

def zeroSumSpace : Submodule ℝ (X → ℝ) :=
  LinearMap.ker (∑ i : X, LinearMap.proj i)

@[simp] theorem mem_zeroSumSpace (x : X → ℝ) :
    x ∈ zeroSumSpace X ↔ ∑ i, x i = 0 := by
  simp [zeroSumSpace, LinearMap.mem_ker]

theorem sum_kSubset_sums (k : ℕ) (hk : 0 < k) (x : X → ℝ) :
    (∑ S : KSubset X k, ∑ i ∈ S.val, x i) =
      ((Fintype.card X - 1).choose (k - 1) : ℝ) * ∑ i, x i := by
  let F := (univ : Finset X).powersetCard k
  change (∑ S : F, ∑ i ∈ S.val, x i) = _
  rw [Finset.sum_coe_sort F (fun S : Finset X => ∑ i ∈ S, x i)]
  calc
    (∑ S ∈ F, ∑ i ∈ S, x i) =
        ∑ S ∈ F, ∑ i : X, if i ∈ S then x i else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      simp
    _ = ∑ i : X, ∑ S ∈ F, if i ∈ S then x i else 0 := Finset.sum_comm
    _ = ∑ i : X, (((F.filter (fun S => i ∈ S)).card : ℕ) : ℝ) * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp
    _ = ∑ i : X, ((Fintype.card X - 1).choose (k - 1) : ℝ) * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hc := Finset.card_filter_powersetCard_subset ({i} : Finset X) univ k
        (by simp) (by simp; omega)
      simpa [F] using congrArg (fun n : ℕ => (n : ℝ) * x i) hc
    _ = _ := (Finset.mul_sum _ _ _).symm

def subsetForms (k : ℕ) : zeroSumSpace X →ₗ[ℝ] (KSubset X k → ℝ) :=
  LinearMap.pi fun S => (∑ i ∈ S.val, LinearMap.proj i).comp (zeroSumSpace X).subtype

@[simp] theorem subsetForms_apply (k : ℕ) (x : zeroSumSpace X) (S : KSubset X k) :
    subsetForms X k x S = ∑ i ∈ S.val, (x : X → ℝ) i := by
  simp [subsetForms]

theorem subsetForms_sum_zero (k : ℕ) (hk : 0 < k) (x : zeroSumSpace X) :
    ∑ S, subsetForms X k x S = 0 := by
  simp only [subsetForms_apply, sum_kSubset_sums X k hk,
    (mem_zeroSumSpace X x).mp x.property, mul_zero]

theorem subsetForms_injective (k : ℕ) (hk : 0 < k) (hkn : k < Fintype.card X) :
    Function.Injective (subsetForms X k) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  have hs (S : KSubset X k) : ∑ i ∈ S.val, (x : X → ℝ) i = 0 := by
    have he := congrFun (LinearMap.mem_ker.mp hx) S
    simpa only [subsetForms_apply, Pi.zero_apply] using he
  have heq (i j : X) : (x : X → ℝ) i = (x : X → ℝ) j := by
    by_cases hij : i = j
    · simpa [hij]
    have hj : j ∈ (univ : Finset X).erase i := by simp [hij, Ne.symm hij]
    have hc : k - 1 ≤ (((univ : Finset X).erase i).erase j).card := by
      rw [card_erase_of_mem hj, card_erase_of_mem (mem_univ i), card_univ]
      omega
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hc
    have hiT : i ∉ T := by
      intro hi
      exact (mem_erase.mp ((erase_subset j _) (hT hi))).1 rfl
    have hjT : j ∉ T := by
      intro hj'
      exact (mem_erase.mp (hT hj')).1 rfl
    have hki : (insert i T).card = k := by rw [card_insert_of_notMem hiT, hTc]; omega
    have hkj : (insert j T).card = k := by rw [card_insert_of_notMem hjT, hTc]; omega
    have hsi := hs ⟨insert i T, mem_powersetCard.mpr ⟨subset_univ _, hki⟩⟩
    have hsj := hs ⟨insert j T, mem_powersetCard.mpr ⟨subset_univ _, hkj⟩⟩
    simp only [sum_insert hiT, sum_insert hjT] at hsi hsj
    linarith
  have hn : 0 < Fintype.card X := lt_trans hk hkn
  haveI : Nonempty X := Fintype.card_pos_iff.mp hn
  let i : X := Classical.choice inferInstance
  have hz := (mem_zeroSumSpace X x).mp x.property
  have hc : (Fintype.card X : ℝ) * x.val i = 0 := by
    calc
      (Fintype.card X : ℝ) * x.val i = ∑ j : X, x.val i := by simp
      _ = ∑ j : X, x.val j := Finset.sum_congr rfl fun j _ => (heq j i).symm
      _ = 0 := hz
  have hxi : x.val i = 0 := (mul_eq_zero.mp hc).resolve_left (by exact_mod_cast hn.ne')
  apply Subtype.ext
  funext j
  exact (heq j i).trans hxi

theorem exists_subsetExponential_minimum (k : ℕ) (hk : 0 < k)
    (hkn : k < Fintype.card X) (c : KSubset X k → ℝ) (hc : ∀ S, 0 < c S) :
    ∃ x : zeroSumSpace X, ∀ y : zeroSumSpace X,
      exponentialSum (subsetForms X k) c x ≤ exponentialSum (subsetForms X k) c y := by
  haveI : Nonempty (KSubset X k) := by
    apply Finset.Nonempty.to_subtype
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hb := Finset.powersetCard_eq_empty.mp he
    simp only [card_univ] at hb
    omega
  exact exists_exponentialSum_minimum (subsetForms X k) (subsetForms_injective X k hk hkn)
    (subsetForms_sum_zero X k hk) c hc

end Bier.Forster
