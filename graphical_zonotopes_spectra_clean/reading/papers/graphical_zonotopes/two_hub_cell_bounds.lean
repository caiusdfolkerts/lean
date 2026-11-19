module

public import Papers.GraphicalZonotopes.TwoHubModuleBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset BooleanModule SetFunctionEmbedding
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem distance_add_missing_le_card (ε Y : Finset I) :
    distance ε Y+((univ\ε)\Y).card≤Fintype.card I := by
  have h0 := card_sdiff_add_card_inter (univ\ε) Y
  have h1 := card_sdiff_add_card_inter ε Y
  have h2 := card_sdiff_add_card_inter (univ : Finset I) ε
  have he : (univ\ε)∩Y=Y\ε := by ext i; simp [and_comm]
  rw [he] at h0
  simp only [univ_inter,card_univ] at h2
  unfold distance
  omega

theorem Cell.missing_zero_count (C : Cell I) (Y : Finset I) :
    ((univ\C.assignment)\C.pull Y).card=
      (univ.filter (fun i : I => i∈C.fixed ∧ i∉C.ones ∧ i∉Y)).card := by
  let e : C.fixed ↪ I := ⟨Subtype.val,Subtype.val_injective⟩
  have he : (((univ\C.assignment)\C.pull Y).map e)=
      univ.filter (fun i : I => i∈C.fixed ∧ i∉C.ones ∧ i∉Y) := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
      simp only [mem_sdiff,mem_univ,true_and,Cell.mem_assignment,Cell.mem_pull] at hj
      exact mem_filter.mpr ⟨mem_univ _,j.2,hj⟩
    · intro hi
      obtain ⟨hfix,hones,hY⟩ := (mem_filter.mp hi).2
      exact mem_map.mpr ⟨⟨i,hfix⟩,by simp [hones,hY],rfl⟩
  have h := congrArg Finset.card he
  simpa only [card_map] using h

theorem Cell.distance_missing_le_fixed (C : Cell I) (Y : Finset I) :
    (distance C.assignment (C.pull Y) : ℝ)+
      ∑ i : I,(if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)*
        (if i∈Y then 0 else 1)≤(C.fixed.card : ℝ) := by
  have hs : (∑ i : I,(if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)*
        (if i∈Y then 0 else 1))=
      ((univ.filter (fun i : I => i∈C.fixed ∧ i∉C.ones ∧ i∉Y)).card : ℝ) := by
    have he : (∑ i : I,(if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)*
        (if i∈Y then 0 else 1))=
        ∑ i : I,if i∈C.fixed ∧ i∉C.ones ∧ i∉Y then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro i hi
      by_cases hf : i∈C.fixed <;> by_cases ho : i∈C.ones <;>
        by_cases hy : i∈Y <;> simp [hf,ho,hy]
    rw [he]
    simp
  rw [hs,←C.missing_zero_count Y]
  have h := distance_add_missing_le_card C.assignment (C.pull Y)
  simpa only [Fintype.card_coe,Nat.cast_add] using (Nat.cast_le.mpr h :
    ((distance C.assignment (C.pull Y)+((univ\C.assignment)\C.pull Y).card : ℕ) : ℝ)≤_)

theorem Cell.ab_delta_distance (C : Cell I) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) :
    delta C.function a b S=(distance C.assignment (C.pull (outers S)) : ℝ)-1 := by
  change delta (extend C.embedding (moduleFunction C.assignment))
    (C.embedding a) (C.embedding b) S=_
  rw [delta_extend]
  have hd := module_ab_distance C.assignment (C.pull (outers S))
  rw [←C.pullSet_outers S] at hd
  rw [←outer_context_of_hubs_absent (pullSet C.embedding S)
    (by simpa using ha) (by simpa using hb)] at hd
  simpa only [C.pullSet_outers S] using hd

theorem Cell.ai_delta_all (C : Cell I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    delta C.function a (u i) S=
      if i∈C.fixed then
        (if i∈C.ones then (if b∈S then 0 else 1) else (if b∈S then 1 else 0)) else 0 := by
  by_cases hc : i∈C.fixed
  · let j : C.fixed := ⟨i,hc⟩
    change delta (extend C.embedding (moduleFunction C.assignment))
      (C.embedding a) (C.embedding (u j)) S=_
    rw [delta_extend,module_ai_delta C.assignment j _ (by simpa using ha)
      (by simpa [j] using hi)]
    simp [hc,j,Cell.pullSet_b]
  · have hh : u i∉Set.range C.embedding := fun h => hc ((C.range_u i).mp h)
    rw [delta_comm]
    change delta (extend C.embedding _) (u i) a S=_
    rw [delta_extend_not_range C.embedding _ _ _ hh]
    simp [hc]

theorem Cell.bi_delta_all (C : Cell I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    delta C.function b (u i) S=
      if i∈C.fixed then (if a∈S then 0 else (if i∈C.ones then 1 else -1)) else 0 := by
  by_cases hc : i∈C.fixed
  · let j : C.fixed := ⟨i,hc⟩
    change delta (extend C.embedding (moduleFunction C.assignment))
      (C.embedding b) (C.embedding (u j)) S=_
    rw [delta_extend,module_bi_delta C.assignment j _ (by simpa using hb)
      (by simpa [j] using hi)]
    simp [hc,j,Cell.pullSet_a]
  · have hh : u i∉Set.range C.embedding := fun h => hc ((C.range_u i).mp h)
    rw [delta_comm]
    change delta (extend C.embedding _) (u i) b S=_
    rw [delta_extend_not_range C.embedding _ _ _ hh]
    simp [hc]

theorem Cell.ai_positive_plus_missing (C : Cell I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    max 0 (delta C.function a (u i) S)+
      (if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)*(if b∈S then 0 else 1)≤
      if i∈C.fixed then 1 else 0 := by
  rw [C.ai_delta_all i S ha hi]
  by_cases hf : i∈C.fixed <;> by_cases ho : i∈C.ones <;> by_cases hb : b∈S <;>
    norm_num [hf,ho,hb]

theorem Cell.bi_positive_plus_missing (C : Cell I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)+
      max 0 (delta C.function b (u i) S)≤if i∈C.fixed then 1 else 0 := by
  rw [C.bi_delta_all i S hb hi]
  by_cases hf : i∈C.fixed <;> by_cases ho : i∈C.ones <;> by_cases ha : a∈S <;>
    norm_num [hf,ho,ha]

end GraphicalZonotopes.TwoHub
