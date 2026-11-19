module

public import Papers.GraphicalZonotopes.TwoHubPrivate

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem bool_set_without_false {X : Finset Bool} (h : false∉X) :
    X=∅ ∨ X={true} := by
  by_cases ht : true∈X
  · right
    ext v
    cases v <;> simp [h,ht]
  · left
    ext v
    cases v <;> simp [h,ht]

theorem bool_set_without_true {X : Finset Bool} (h : true∉X) :
    X=∅ ∨ X={false} := by
  by_cases ht : false∈X
  · right
    ext v
    cases v <;> simp [h,ht]
  · left
    ext v
    cases v <;> simp [h,ht]

theorem signed_sum_card (ε Y : Finset I) :
    (∑ i∈Y,if i∈ε then (-1 : ℝ) else 1)=
      ((Y\ε).card : ℝ)-((Y∩ε).card : ℝ) := by
  have hp : Y.filter (fun i => i∈ε)=Y∩ε := by ext i; simp
  have hn : Y.filter (fun i => i∉ε)=Y\ε := by ext i; simp
  rw [sum_ite,hp,hn]
  simp
  <;> ring

theorem reverse_signed_sum_card (ε Y : Finset I) :
    (∑ i∈Y,if i∈ε then (1 : ℝ) else -1)=
      ((Y∩ε).card : ℝ)-((Y\ε).card : ℝ) := by
  have hp : Y.filter (fun i => i∈ε)=Y∩ε := by ext i; simp
  have hn : Y.filter (fun i => i∉ε)=Y\ε := by ext i; simp
  rw [sum_ite,hp,hn]
  simp
  <;> ring

@[simp] theorem eta_nonneg (ε : Finset I) : 0≤eta ε := by
  unfold eta
  split_ifs <;> norm_num

theorem eta_card_sub_one_nonneg (ε : Finset I) : 0≤eta ε+(ε.card : ℝ)-1 := by
  by_cases h : ε=∅
  · simp [h,eta]
  · have hc : 1≤ε.card := card_pos.mpr (nonempty_iff_ne_empty.mpr h)
    have hc' : (1 : ℝ)≤(ε.card : ℝ) := by exact_mod_cast hc
    simp only [eta,if_neg h,zero_add]
    linarith

/-- Nonnegative first differences of the integer-valued module (8.1),
including the endpoint p=1 and all conditioning sets. -/
theorem module_cover_nonnegative [Nonempty I] (ε : Finset I) (v : Hub I)
    (S : Finset (Hub I)) :
    0 ≤ moduleFunction ε (insert v S)-moduleFunction ε S := by
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
    exact corner_nonneg _ _
  | inl v =>
    have hX : v∉X := by simpa using hv
    rw [←context_insert_hub]
    cases v with
    | false =>
      rcases bool_set_without_false hX with hX0 | hX1
      · rw [hX0,insert_empty_eq,module_a_zero_cover]
        exact add_nonneg (eta_nonneg ε) (sum_nonneg (by intro i hi; split_ifs <;> norm_num))
      · have hb : insert false ({true} : Finset Bool)=univ := by decide
        rw [hX1,hb,module_a_one_cover]
        exact add_nonneg (eta_card_sub_one_nonneg ε)
          (sum_nonneg (by intro i hi; split_ifs <;> norm_num))
    | true =>
      rcases bool_set_without_true hX with hX0 | hX1
      · rw [hX0,insert_empty_eq,module_b_zero_cover,reverse_signed_sum_card]
        have hsub : Y\ε ⊆ univ\ε := sdiff_subset_sdiff (subset_univ Y) Subset.rfl
        have hc := card_le_card hsub
        have hc' : ((Y\ε).card : ℝ)≤(Fintype.card I : ℝ)-(ε.card : ℝ) := by
          have hh : ((Y\ε).card : ℝ)≤((univ\ε).card : ℝ) := by exact_mod_cast hc
          simpa only [card_sdiff_of_subset (subset_univ ε),card_univ,Nat.cast_sub (card_le_univ ε)] using hh
        linarith [(Nat.cast_nonneg ((Y∩ε).card) : (0 : ℝ)≤((Y∩ε).card : ℝ))]
      · have hb : insert true ({false} : Finset Bool)=univ := by decide
        rw [hX1,hb,module_b_one_cover]
        have hp : (1 : ℝ)≤(Fintype.card I : ℝ) := by
          exact_mod_cast (Fintype.card_pos : 0<Fintype.card I)
        linarith

def distance (ε Y : Finset I) : ℕ := (ε\Y).card+(Y\ε).card

theorem distance_zero_iff (ε Y : Finset I) : distance ε Y=0 ↔ ε=Y := by
  simp only [distance,Nat.add_eq_zero,card_eq_zero,sdiff_eq_empty_iff_subset]
  exact ⟨fun h => Subset.antisymm h.1 h.2,fun h => by simp [h]⟩

theorem module_ab_distance (ε Y : Finset I) :
    delta (moduleFunction ε) a b (outerSet Y)=(distance ε Y : ℝ)-1 := by
  rw [module_ab,signed_sum_card]
  have hc : ((ε\Y).card : ℝ)+((Y∩ε).card : ℝ)=(ε.card : ℝ) := by
    exact_mod_cast (by simpa only [inter_comm] using card_sdiff_add_card_inter ε Y)
  simp only [distance,Nat.cast_add]
  linarith

theorem module_ab_negativeResponse (ε Y : Finset I) :
    negativeResponse (moduleFunction ε) a b (outerSet Y)=if Y=ε then 1 else 0 := by
  rw [negativeResponse,module_ab_distance]
  by_cases he : Y=ε
  · subst Y
    simp [distance]
  · have hd : 1≤distance ε Y := Nat.one_le_iff_ne_zero.mpr
      (fun hh => he ((distance_zero_iff ε Y).mp hh).symm)
    have hd' : (1 : ℝ)≤(distance ε Y : ℝ) := by exact_mod_cast hd
    rw [if_neg he,max_eq_left (by linarith)]

theorem module_ai_delta (ε : Finset I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    delta (moduleFunction ε) a (u i) S=
      if i∈ε then (if b∈S then 0 else 1) else (if b∈S then 1 else 0) := by
  have hx : false∉hubs S := by simpa [a] using ha
  simp only [moduleFunction,a,u,delta_assembled_spoke _ _ _ _ _ _ hi,one_mul]
  by_cases hb : b∈S <;> by_cases he : i∈ε <;>
    simp [corner,hx,he,show (true∈hubs S ↔ b∈S) from by simp [b],hb]

theorem module_bi_delta (ε : Finset I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    delta (moduleFunction ε) b (u i) S=
      if a∈S then 0 else (if i∈ε then 1 else -1) := by
  have hx : true∉hubs S := by simpa [b] using hb
  simp only [moduleFunction,b,u,delta_assembled_spoke _ _ _ _ _ _ hi,one_mul]
  by_cases ha : a∈S <;> by_cases he : i∈ε <;>
    simp [corner,hx,he,show (false∈hubs S ↔ a∈S) from by simp [a],ha]

theorem module_ai_response (ε : Finset I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : negativeResponse (moduleFunction ε) a (u i) S=0 := by
  rw [negativeResponse,module_ai_delta ε i S ha hi]
  split_ifs <;> norm_num

theorem module_bi_response (ε : Finset I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    negativeResponse (moduleFunction ε) b (u i) S=
      if i∈ε then 0 else (if a∈S then 0 else 1) := by
  rw [negativeResponse,module_bi_delta ε i S hb hi]
  split_ifs <;> norm_num

/-- The balancing Boolean module r_i = a(b ∨ u_i). -/
def balancing (i : I) : SetFunction (Hub I) :=
  fun S => if a∈S ∧ (b∈S ∨ u i∈S) then 1 else 0

theorem balancing_boolean (i : I) : IsMonotoneBoolean (balancing i) where
  monotone := by
    intro X Y hXY
    unfold balancing
    split_ifs with hX hY hY
    · exact le_refl _
    · exact False.elim (hY ⟨hXY hX.1,hX.2.imp (fun h => hXY h) (fun h => hXY h)⟩)
    · norm_num
    · norm_num
  values := by intro X; unfold balancing; split_ifs <;> simp
  empty := by simp [balancing]
  full := by simp [balancing]

theorem balancing_ab_delta (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) :
    delta (balancing i) a b S=if u i∈S then 0 else 1 := by
  by_cases hi : u i∈S <;> simp_all [delta,balancing,a,b,u] <;> ring

theorem balancing_ai_delta (i j : I) (S : Finset (Hub I))
    (ha : a∉S) (hj : u j∉S) :
    delta (balancing i) a (u j) S=if i=j then (if b∈S then 0 else 1) else 0 := by
  by_cases he : i=j
  · subst j
    by_cases hb : b∈S <;> simp_all [delta,balancing,a,b,u] <;> ring
  · by_cases hb : b∈S <;> by_cases hi : u i∈S <;>
      simp_all [delta,balancing,a,b,u,Ne.symm he] <;> ring

theorem balancing_bi_delta (i j : I) (S : Finset (Hub I))
    (hb : b∉S) (hj : u j∉S) :
    delta (balancing i) b (u j) S=if i=j then (if a∈S then -1 else 0) else 0 := by
  by_cases he : i=j
  · subst j
    by_cases ha : a∈S <;> simp_all [delta,balancing,a,b,u] <;> ring
  · by_cases ha : a∈S <;> by_cases hi : u i∈S <;>
      simp_all [delta,balancing,a,b,u,Ne.symm he] <;> ring

theorem balancing_outer_zero (i : I) : OuterZero (balancing i) := by
  intro j k hjk S hj hk
  by_cases hij : i=j <;> by_cases hik : i=k <;>
    by_cases ha : a∈S <;> by_cases hb : b∈S <;> by_cases hi : u i∈S <;>
    simp_all [delta,balancing,a,b,u]

end TwoHub
end GraphicalZonotopes
