module

public import Papers.GraphicalZonotopes.TwoHubRestriction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset BooleanModule SetFunctionEmbedding
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem present_indicator_sum (ε Y : Finset I) :
    (∑ i∈Y,if i∈ε then (1 : ℝ) else 0)=((Y∩ε).card : ℝ) := by
  have hp : Y.filter (fun i => i∈ε)=Y∩ε := by ext i; simp
  rw [←sum_filter,hp]
  simp

theorem absent_indicator_sum (ε Y : Finset I) :
    (∑ i∈Y,if i∈ε then (0 : ℝ) else 1)=((Y\ε).card : ℝ) := by
  have hn : Y.filter (fun i => i∉ε)=Y\ε := by ext i; simp
  have he : (∑ i∈Y,if i∈ε then (0 : ℝ) else 1)=
      ∑ i∈Y,if i∉ε then (1 : ℝ) else 0 := by
    apply sum_congr rfl
    intro i hi
    by_cases he : i∈ε <;> simp [he]
  rw [he,←sum_filter,hn]
  simp

/-- A single private spoke of module (8.1) is bounded by the number of
coordinates that the module actually uses, including the endpoint one. -/
theorem module_cover_le_card [Nonempty I] (ε : Finset I) (v : Hub I)
    (S : Finset (Hub I)) :
    moduleFunction ε (insert v S)-moduleFunction ε S≤(Fintype.card I : ℝ) := by
  have hp : (1 : ℝ)≤(Fintype.card I : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card I)
  by_cases hv : v∈S
  · simp [insert_eq_of_mem hv]
  let X:=hubs S
  let Y:=outers S
  have hS : context X Y=S := context_parts S
  rw [←hS] at hv ⊢
  cases v with
  | inr i =>
    have hi : i∉Y := by simpa using hv
    rw [moduleFunction,←context_insert,privateSlice_context _ _ _ _ _ _ hi,one_mul]
    rcases corner_values (decide (i∈ε)) X with h|h <;> rw [h] <;> linarith
  | inl v =>
    have hX : v∉X := by simpa using hv
    rw [←context_insert_hub]
    cases v with
    | false =>
      rcases bool_set_without_false hX with hX0|hX1
      · rw [hX0,insert_empty_eq,module_a_zero_cover,present_indicator_sum]
        by_cases he : ε=∅
        · simp only [he,eta,ite_true,inter_empty,card_empty,Nat.cast_zero,add_zero]
          exact hp
        · have hc : ((Y∩ε).card : ℝ)≤(Fintype.card I : ℝ) := by
            exact_mod_cast card_le_univ (Y∩ε)
          simpa only [eta,if_neg he,zero_add] using hc
      · have hb : insert false ({true} : Finset Bool)=univ := by decide
        rw [hX1,hb,module_a_one_cover,absent_indicator_sum]
        have hs : Y\ε⊆univ\ε := sdiff_subset_sdiff (subset_univ Y) Subset.rfl
        have hc : ((Y\ε).card : ℝ)≤(Fintype.card I : ℝ)-(ε.card : ℝ) := by
          have hh : ((Y\ε).card : ℝ)≤((univ\ε).card : ℝ) := by exact_mod_cast card_le_card hs
          simpa only [card_sdiff_of_subset (subset_univ ε),card_univ,
            Nat.cast_sub (card_le_univ ε)] using hh
        have he : eta ε≤1 := by unfold eta; split_ifs <;> norm_num
        linarith
    | true =>
      rcases bool_set_without_true hX with hX0|hX1
      · rw [hX0,insert_empty_eq,module_b_zero_cover,reverse_signed_sum_card]
        have hc : ((Y∩ε).card : ℝ)≤(ε.card : ℝ) := by
          exact_mod_cast card_le_card (inter_subset_right : Y∩ε⊆ε)
        have hn : (0 : ℝ)≤((Y\ε).card : ℝ) := Nat.cast_nonneg _
        linarith
      · have hb : insert true ({false} : Finset Bool)=univ := by decide
        rw [hX1,hb,module_b_one_cover]
        linarith

theorem Cell.cover_le_fixed_card (C : Cell I) (hC : C.fixed.Nonempty)
    (v : Hub I) (S : Finset (Hub I)) :
    C.function (insert v S)-C.function S≤(C.fixed.card : ℝ) := by
  letI : Nonempty C.fixed := ⟨⟨hC.choose,hC.choose_spec⟩⟩
  by_cases hv : v∈Set.range C.embedding
  · obtain ⟨w,rfl⟩ := hv
    simpa only [Cell.function,extend,pullSet_insert_image,Fintype.card_coe] using
      module_cover_le_card C.assignment w (pullSet C.embedding S)
  · simp only [Cell.function,extend_insert_absent C.embedding _ v hv S,sub_self]
    exact Nat.cast_nonneg _

end GraphicalZonotopes.TwoHub
