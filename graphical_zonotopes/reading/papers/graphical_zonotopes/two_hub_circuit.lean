module

public import Papers.GraphicalZonotopes.TwoHubResponses

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The response identity is independent of the ordering of the three
variables. It is the discrete equality of mixed third derivatives. -/
theorem delta_insert_difference (f : SetFunction (Hub I)) (x y z : Hub I)
    (S : Finset (Hub I)) :
    delta f x y (insert z S)-delta f x y S=
      delta f x z (insert y S)-delta f x z S := by
  simp only [delta]
  simp only [insert_comm y z]
  ring

theorem outer_context_of_hubs_absent (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    S=outerSet (outers S) := by
  have hX : hubs S=∅ := by
    ext v
    cases v <;> simp_all [a,b]
  have h:=context_parts S
  rw [hX] at h
  simpa [context] using h.symm

theorem module_ab_response_all (ε : Finset I) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) :
    negativeResponse (moduleFunction ε) a b S=if outers S=ε then 1 else 0 := by
  conv_lhs => rw [outer_context_of_hubs_absent S ha hb]
  exact module_ab_negativeResponse ε (outers S)

theorem balancing_ab_response (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) : negativeResponse (balancing i) a b S=0 := by
  rw [negativeResponse,balancing_ab_delta i S ha hb]
  split_ifs <;> norm_num

theorem balancing_ai_response (i j : I) (S : Finset (Hub I))
    (ha : a∉S) (hj : u j∉S) : negativeResponse (balancing i) a (u j) S=0 := by
  rw [negativeResponse,balancing_ai_delta i j S ha hj]
  split_ifs <;> norm_num

theorem balancing_bi_response (i j : I) (S : Finset (Hub I))
    (hb : b∉S) (hj : u j∉S) :
    negativeResponse (balancing i) b (u j) S=if i=j then (if a∈S then 1 else 0) else 0 := by
  rw [negativeResponse,balancing_bi_delta i j S hb hj]
  split_ifs <;> norm_num

abbrev Index (I : Type*) := Finset I⊕I

def family : Index I → SetFunction (Hub I)
  | .inl ε => moduleFunction ε
  | .inr i => balancing i

def missCount (i : I) : ℕ := (univ.filter (fun ε : Finset I => i∉ε)).card

theorem missCount_eq (i : I) : missCount i=2^(Fintype.card I-1) := by
  have he : (univ.filter (fun ε : Finset I => i∉ε))=(univ.erase i).powerset := by
    ext ε
    simp only [mem_filter,mem_univ,true_and,mem_powerset,subset_erase,subset_univ,and_true]
  rw [missCount,he,card_powerset,card_erase_of_mem (mem_univ i),card_univ]

theorem missCount_pos (i : I) : 0 < missCount i := by
  rw [missCount_eq]
  positivity

def weights : Index I → ℝ
  | .inl _ => 1
  | .inr i => (missCount i : ℝ)

def boundaryCentral : SetFunction (Hub I) :=
  assembled (pair 0 0 1) (fun i X => if true∈X then (missCount i : ℝ) else 0) (fun _ => 1)

def construction : SetFunction (Hub I⊕Index I) := assembled boundaryCentral family weights

theorem weights_pos (j : Index I) : 0 < weights j := by
  cases j with
  | inl ε => norm_num [weights]
  | inr i => simpa [weights] using (Nat.cast_pos.mpr (missCount_pos i) : (0 : ℝ)<(missCount i : ℝ))

theorem family_empty (j : Index I) : family j ∅=0 := by
  cases j with
  | inl ε => exact module_empty ε
  | inr i => exact (balancing_boolean i).empty

theorem family_monotone [Nonempty I] (j : Index I) (v : Hub I) (S : Finset (Hub I)) :
    0≤family j (insert v S)-family j S := by
  cases j with
  | inl ε => exact module_cover_nonnegative ε v S
  | inr i => exact sub_nonneg.mpr ((balancing_boolean i).monotone (subset_insert v S))

theorem family_privateRigid [Nonempty I] (j : Index I) : PrivateRigid (family j) := by
  cases j with
  | inl ε => exact module_private_rigid ε
  | inr i => exact (balancing_boolean i).privateRigid

theorem family_ai_response (j : Index I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : negativeResponse (family j) a (u i) S=0 := by
  cases j with
  | inl ε => exact module_ai_response ε i S ha hi
  | inr k => exact balancing_ai_response k i S ha hi

theorem response_sum_ab (t : Index I → ℝ) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) :
    (∑ j : Index I,t j*negativeResponse (family j) a b S)=t (.inl (outers S)) := by
  rw [Fintype.sum_sum_type]
  simp only [family,module_ab_response_all _ _ ha hb,balancing_ab_response _ _ ha hb,
    mul_zero,sum_const_zero,add_zero,mul_ite,mul_one]
  simp

theorem response_sum_ai (t : Index I → ℝ) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    (∑ j : Index I,t j*negativeResponse (family j) a (u i) S)=0 := by
  simp only [family_ai_response _ _ _ ha hi,mul_zero,sum_const_zero]

theorem response_sum_bi (t : Index I → ℝ) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (∑ j : Index I,t j*negativeResponse (family j) b (u i) S)=
      if a∈S then t (.inr i) else ∑ ε : Finset I,if i∈ε then 0 else t (.inl ε) := by
  rw [Fintype.sum_sum_type]
  simp only [family,module_bi_response _ _ _ hb hi,balancing_bi_response _ _ _ hb hi]
  by_cases ha : a∈S
  · simp [ha]
  · simp [ha,mul_ite]

theorem family_outer_response (j : Index I) (i k : I) (hik : i≠k)
    (S : Finset (Hub I)) (hi : u i∉S) (hk : u k∉S) :
    negativeResponse (family j) (u i) (u k) S=0 := by
  cases j with
  | inl ε =>
    rw [family,negativeResponse]
    change max 0 (-delta (moduleFunction ε) (.inr i) (.inr k) S)=0
    rw [module_outer_zero ε i k hik S hi hk,neg_zero,max_self]
  | inr v =>
    rw [family,negativeResponse]
    change max 0 (-delta (balancing v) (.inr i) (.inr k) S)=0
    rw [balancing_outer_zero v i k hik S hi hk,neg_zero,max_self]

theorem compatible_ai_zero {h : SetFunction (Hub I)} {t : Index I → ℝ}
    (hc : Compatible h family t) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : delta h a (u i) S=0 := by
  rw [hc a (u i) (by simp [a,u]) S ha hi,response_sum_ai _ _ _ ha hi]

theorem compatible_ab_constant {h : SetFunction (Hub I)} {t : Index I → ℝ}
    (hc : Compatible h family t) (Y : Finset I) :
    delta h a b (outerSet Y)=delta h a b ∅ := by
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert i Y hi ih =>
    rw [outerSet_insert]
    have hh:=delta_insert_difference h a b (u i) (outerSet Y)
    have hz0:=compatible_ai_zero hc i (outerSet Y) (by simp [a]) (by simpa [u] using hi)
    have hz1:=compatible_ai_zero hc i (insert b (outerSet Y))
      (by simp [a,b]) (by simpa [u,b] using hi)
    rw [hz0,hz1] at hh
    change delta h a b (insert (u i) (outerSet Y))=delta h a b ∅
    rw [←ih]
    linarith

/-- Exact one-dimensionality of the integrability relation space. The
central function is arbitrary; no coefficient ansatz is imposed. -/
theorem unique_relation : UniqueIntegrableRelation (family (I:=I)) weights := by
  intro t ht
  obtain ⟨h,hn,hc⟩:=ht
  let c:=delta h a b ∅
  have hm (ε : Finset I) : t (.inl ε)=c := by
    have he:=hc a b (by simp [a,b]) (outerSet ε) (by simp [a]) (by simp [b])
    rw [response_sum_ab _ _ (by simp [a]) (by simp [b])] at he
    have hε : outers (outerSet (H:=Bool) ε)=ε := by ext i; simp
    rw [hε] at he
    exact he.symm.trans (compatible_ab_constant hc ε)
  have hb (i : I) : t (.inr i)=(missCount i : ℝ)*c := by
    have hz0:=compatible_ai_zero hc i (∅ : Finset (Hub I)) (by simp) (by simp)
    have hz1:=compatible_ai_zero hc i {b} (by simp [a,b]) (by simp [b,u])
    have hd:=delta_insert_difference h (u i) b a ∅
    rw [delta_comm (u i) b,delta_comm (u i) b,delta_comm (u i) a,delta_comm (u i) a] at hd
    simp only [insert_empty_eq] at hd
    rw [hz0,hz1] at hd
    have h0:=hc b (u i) (by simp [b,u]) ∅ (by simp) (by simp)
    have h1:=hc b (u i) (by simp [b,u]) {a} (by simp [a,b]) (by simp [a,u])
    rw [response_sum_bi _ _ _ (by simp) (by simp)] at h0
    rw [response_sum_bi _ _ _ (by simp [a,b]) (by simp [a,u])] at h1
    simp only [notMem_empty,not_false_eq_true,if_false,mem_singleton,ite_true] at h0 h1
    have hs : (∑ ε : Finset I,if i∈ε then (0 : ℝ) else t (.inl ε))=(missCount i : ℝ)*c := by
      simp_rw [hm]
      have he : (∑ ε : Finset I,if i∈ε then (0 : ℝ) else c)=
          ∑ ε∈univ.filter (fun ε : Finset I => i∉ε),c := by
        rw [sum_filter]
        apply sum_congr rfl
        intro ε hε
        by_cases hi : i∈ε <;> simp [hi]
      rw [he]
      simp only [sum_const,nsmul_eq_mul,missCount]
    rw [hs] at h0
    linarith
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl ε => simpa [weights] using hm ε
  | inr i => simpa [weights,mul_comm] using hb i

end TwoHub
end GraphicalZonotopes
