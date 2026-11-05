module

public import Papers.GraphicalZonotopes.TwoHubGeometry
public import Papers.GraphicalZonotopes.LatticeExtremeEmbedding

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

def dilation (p : ℕ) : ℕ := (p-1)*2^p+2

theorem two_mul_missCount (i : I) : 2*missCount i=2^Fintype.card I := by
  have hp : 0<Fintype.card I:=Fintype.card_pos_iff.mpr ⟨i⟩
  rw [missCount_eq,mul_comm,←pow_succ]
  congr 1
  omega

theorem presentCount_eq (i : I) :
    (univ.filter (fun ε : Finset I => i∈ε)).card=missCount i := by
  have hh:=card_filter_add_card_filter_not (s:=(univ : Finset (Finset I))) (fun ε => i∈ε)
  have ht:=two_mul_missCount i
  simp only [card_univ,Fintype.card_finset] at hh
  change (univ.filter (fun ε : Finset I => i∈ε)).card+missCount i=2^Fintype.card I at hh
  omega

theorem present_sum (i : I) :
    (∑ ε : Finset I,if i∈ε then (1 : ℝ) else 0)=(missCount i : ℝ) := by
  rw [←sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one,presentCount_eq]

theorem distance_sum (Y : Finset I) :
    (∑ ε : Finset I,(distance ε Y : ℝ))=
      (Fintype.card I : ℝ)*(2^(Fintype.card I-1) : ℝ) := by
  have hdist (ε : Finset I) : (distance ε Y : ℝ)=
      ∑ i : I,if i∈Y then (if i∈ε then 0 else 1) else (if i∈ε then 1 else 0) := by
    have h0 : ε\Y=univ.filter (fun i => i∈ε ∧ i∉Y):=by ext i; simp
    have h1 : Y\ε=univ.filter (fun i => i∈Y ∧ i∉ε):=by ext i; simp
    have hcard (A : Finset I) : (A.card : ℝ)=∑ i∈A,(1 : ℝ):=by simp
    rw [distance,Nat.cast_add,hcard,hcard,h0,h1,sum_filter,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases hε : i∈ε <;> by_cases hY : i∈Y <;> simp [hε,hY]
  simp_rw [hdist]
  rw [sum_comm]
  have hb (i : I) :
      (∑ ε : Finset I,if i∈Y then (if i∈ε then (0 : ℝ) else 1) else (if i∈ε then 1 else 0))=
      (2^(Fintype.card I-1) : ℝ) := by
    by_cases hi : i∈Y
    · simp only [hi,ite_true]
      rw [missing_sum,missCount_eq]
      norm_cast
    · simp only [hi,ite_false]
      rw [present_sum,missCount_eq]
      norm_cast
  simp_rw [hb]
  simp

theorem max_zero_eq_add_negative (x : ℝ) : max 0 x=x+max 0 (-x) := by
  by_cases hx : 0≤x
  · rw [max_eq_right hx,max_eq_left (neg_nonpos.mpr hx),add_zero]
  · have hx' : x≤0:=le_of_not_ge hx
    rw [max_eq_left hx',max_eq_right (neg_nonneg.mpr hx')]
    ring

theorem positive_ab_sum (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    (∑ ε : Finset I,max 0 (delta (moduleFunction ε) a b S))=
      (Fintype.card I : ℝ)*(2^(Fintype.card I-1) : ℝ)-(2^Fintype.card I : ℝ)+1 := by
  have he (ε : Finset I) : max 0 (delta (moduleFunction ε) a b S)=
      (distance ε (outers S) : ℝ)-1+(if outers S=ε then 1 else 0) := by
    rw [max_zero_eq_add_negative]
    change delta (moduleFunction ε) a b S+negativeResponse (moduleFunction ε) a b S=_
    rw [module_ab_response_all ε S ha hb]
    have hd:=module_ab_distance ε (outers S)
    rw [←outer_context_of_hubs_absent S ha hb] at hd
    rw [hd]
  simp_rw [he]
  rw [sum_add_distrib,sum_sub_distrib,distance_sum]
  simp

theorem dilation_cast (p : ℕ) (hp : 1≤p) :
    (dilation p : ℝ)=((p : ℝ)-1)*(2^p : ℝ)+2 := by
  simp only [dilation,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp,Nat.cast_one,
    Nat.cast_pow,Nat.cast_ofNat]

theorem two_pow_le_dilation (p : ℕ) (hp : 1≤p) : 2^p≤dilation p := by
  by_cases he : p=1
  · subst p
    decide
  · have h : 1≤p-1:=by omega
    have hm:=Nat.mul_le_mul_right (2^p) h
    simp only [one_mul] at hm
    exact hm.trans (Nat.le_add_right _ _)

theorem two_mul_le_dilation (p : ℕ) (hp : 1≤p) : 2*p≤dilation p := by
  by_cases he : p=1
  · subst p
    decide
  · have hp2 : 2≤p:=by omega
    have hpow : 4≤2^p:=by
      have h:=Nat.pow_le_pow_right (by decide : 1≤(2 : ℕ)) hp2
      simpa using h
    have hh:=Nat.mul_le_mul_left (p-1) hpow
    unfold dilation
    nlinarith [Nat.sub_add_cancel hp]

theorem missCount_le_dilation (i : I) : missCount i≤dilation (Fintype.card I) := by
  have hp : 1≤Fintype.card I:=Fintype.card_pos_iff.mpr ⟨i⟩
  have hm : missCount i≤2^Fintype.card I:=by have ht:=two_mul_missCount i;omega
  exact hm.trans (two_pow_le_dilation _ hp)

/-- A bound on the total range suffices for every private spoke; it avoids
any implicit restriction on its conditioning set. -/
theorem module_cover_le [Nonempty I] (ε : Finset I) (v : Hub I) (S : Finset (Hub I)) :
    moduleFunction ε (insert v S)-moduleFunction ε S≤2*(Fintype.card I : ℝ) := by
  have hstep (X Z : Finset (Hub I)) : moduleFunction ε X≤moduleFunction ε (X∪Z) := by
    induction Z using Finset.induction_on with
    | empty => simp
    | @insert v Z hv ih =>
      rw [union_insert]
      exact ih.trans (sub_nonneg.mp (module_cover_nonnegative ε v (X∪Z)))
  have hm : Monotone (moduleFunction ε):=by
    intro X Y hXY
    simpa only [union_eq_right.mpr hXY] using hstep X Y
  have hn : 0 ≤ moduleFunction ε S := by
    simpa using hm (empty_subset S)
  have hu:=hm (subset_univ (insert v S))
  have hc : context (univ : Finset Bool) (univ : Finset I)=univ := by
    ext x
    cases x <;> simp
  have hfull : moduleFunction ε univ=eta ε+2*(Fintype.card I : ℝ)-1 := by
    rw [←hc,module_context]
    simp only [central,pair,mem_univ,and_self,ite_true,corner_full,sum_const,
      card_univ,nsmul_eq_mul,mul_one]
    ring
  have he : eta ε≤1:=by unfold eta;split_ifs <;> norm_num
  rw [hfull] at hu
  linarith

variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

theorem assembled_hubs_le (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ)
    (hw : ∀ j,0≤w j) (u v : H) (A : Finset (H⊕J)) :
    delta (assembled z F w) (.inl u) (.inl v) A≤
      delta z u v (hubs A)+∑ j,w j*max 0 (delta (F j) u v (hubs A)) := by
  rw [delta_assembled_hubs]
  apply add_le_add (le_refl _)
  apply sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j)
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _


theorem positive_ai_main_sum (i : I) (S : Finset (Hub I)) (ha : a∉S) (hi : u i∉S) :
    (∑ ε : Finset I,max 0 (delta (moduleFunction ε) a (u i) S))=(missCount i : ℝ) := by
  have he (ε : Finset I) : max 0 (delta (moduleFunction ε) a (u i) S)=
      if i∈ε then (if b∈S then 0 else 1) else (if b∈S then 1 else 0) := by
    rw [module_ai_delta ε i S ha hi]
    split_ifs <;> norm_num
  simp_rw [he]
  by_cases hb : b∈S
  · simp only [hb,ite_true]
    exact missing_sum i
  · simp only [hb,ite_false]
    exact present_sum i

theorem positive_bi_main_sum_le (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
    (∑ ε : Finset I,max 0 (delta (moduleFunction ε) b (u i) S))≤(missCount i : ℝ) := by
  have he (ε : Finset I) : max 0 (delta (moduleFunction ε) b (u i) S)=
      if a∈S then 0 else (if i∈ε then 1 else 0) := by
    rw [module_bi_delta ε i S hb hi]
    split_ifs <;> norm_num
  simp_rw [he]
  by_cases ha : a∈S
  · simp [ha]
  · simp only [ha,ite_false,present_sum,le_refl]

theorem positive_ai_extra_sum (i : I) (S : Finset (Hub I)) (ha : a∉S) (hi : u i∉S) :
    (∑ j : I,(missCount j : ℝ)*max 0 (delta (balancing j) a (u i) S))=
      if b∈S then 0 else (missCount i : ℝ) := by
  have he (j : I) : max 0 (delta (balancing j) a (u i) S)=
      if j=i then (if b∈S then 0 else 1) else 0 := by
    rw [balancing_ai_delta j i S ha hi]
    split_ifs <;> norm_num
  simp_rw [he]
  by_cases hb : b∈S <;> simp [hb]

theorem positive_bi_extra_sum (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
    (∑ j : I,(missCount j : ℝ)*max 0 (delta (balancing j) b (u i) S))=0 := by
  apply sum_eq_zero
  intro j hj
  rw [balancing_bi_delta j i S hb hi]
  split_ifs <;> norm_num

theorem positive_ab_extra_sum_le (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    (∑ j : I,(missCount j : ℝ)*max 0 (delta (balancing j) a b S))≤
      (Fintype.card I : ℝ)*(2^(Fintype.card I-1) : ℝ) := by
  calc
    _ ≤ ∑ j : I,(missCount j : ℝ) := by
      apply sum_le_sum
      intro j hj
      rw [balancing_ab_delta j S ha hb]
      split_ifs <;> simp
    _ = _ := by simp only [missCount_eq,Nat.cast_pow,Nat.cast_ofNat,sum_const,
        card_univ,nsmul_eq_mul]

theorem construction_ab_le [Nonempty I] (A : Finset (Hub I⊕Index I))
    (ha : Sum.inl (a : Hub I)∉A) (hb : Sum.inl (b : Hub I)∉A) :
    delta construction (.inl a) (.inl b) A≤(dilation (Fintype.card I) : ℝ) := by
  have ha' : a∉hubs A:=by simpa using ha
  have hb' : b∉hubs A:=by simpa using hb
  have hh:=assembled_hubs_le boundaryCentral family weights (fun j => (weights_pos j).le) a b A
  rw [boundaryCentral_ab _ ha' hb',Fintype.sum_sum_type] at hh
  simp only [family,weights,one_mul] at hh
  rw [positive_ab_sum _ ha' hb'] at hh
  have hbnd:=positive_ab_extra_sum_le (hubs A) ha' hb'
  let i₀ : I:=Classical.choice ‹Nonempty I›
  have ht : (2 : ℝ)*(2^(Fintype.card I-1) : ℝ)=(2^Fintype.card I : ℝ) := by
    have h:=two_mul_missCount i₀
    rw [missCount_eq] at h
    exact_mod_cast h
  have hmul:=congrArg (fun x : ℝ => (Fintype.card I : ℝ)*x) ht
  rw [dilation_cast _ (by have h:=Fintype.card_pos (α:=I);omega)]
  change delta (assembled boundaryCentral family weights) (.inl a) (.inl b) A≤_
  nlinarith

theorem construction_ai_le (i : I) (A : Finset (Hub I⊕Index I))
    (ha : Sum.inl (a : Hub I)∉A) (hi : Sum.inl (u i)∉A) :
    delta construction (.inl a) (.inl (u i)) A≤(dilation (Fintype.card I) : ℝ) := by
  have ha' : a∉hubs A:=by simpa using ha
  have hi' : u i∉hubs A:=by simpa using hi
  have hh:=assembled_hubs_le boundaryCentral family weights (fun j => (weights_pos j).le) a (u i) A
  rw [boundaryCentral_ai _ _ hi',Fintype.sum_sum_type,zero_add] at hh
  simp only [family,weights,one_mul] at hh
  rw [positive_ai_main_sum _ _ ha' hi',positive_ai_extra_sum _ _ ha' hi'] at hh
  have ht : (2 : ℝ)*(missCount i : ℝ)=(2^Fintype.card I : ℝ):=by exact_mod_cast two_mul_missCount i
  have hm : (2^Fintype.card I : ℝ)≤(dilation (Fintype.card I) : ℝ):=by
    exact_mod_cast two_pow_le_dilation (Fintype.card I) (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hn : 0≤(missCount i : ℝ):=Nat.cast_nonneg _
  change delta (assembled boundaryCentral family weights) (.inl a) (.inl (u i)) A≤_
  split_ifs at hh <;> linarith

theorem construction_bi_le (i : I) (A : Finset (Hub I⊕Index I))
    (hb : Sum.inl (b : Hub I)∉A) (hi : Sum.inl (u i)∉A) :
    delta construction (.inl b) (.inl (u i)) A≤(dilation (Fintype.card I) : ℝ) := by
  have hb' : b∉hubs A:=by simpa using hb
  have hi' : u i∉hubs A:=by simpa using hi
  have hh:=assembled_hubs_le boundaryCentral family weights (fun j => (weights_pos j).le) b (u i) A
  rw [boundaryCentral_bi _ _ hb' hi',Fintype.sum_sum_type] at hh
  simp only [family,weights,one_mul] at hh
  rw [positive_bi_extra_sum _ _ hb' hi',add_zero] at hh
  have hp:=positive_bi_main_sum_le i (hubs A) hb' hi'
  have ht : (2 : ℝ)*(missCount i : ℝ)=(2^Fintype.card I : ℝ):=by exact_mod_cast two_mul_missCount i
  have hm : (2^Fintype.card I : ℝ)≤(dilation (Fintype.card I) : ℝ):=by
    exact_mod_cast two_pow_le_dilation (Fintype.card I) (Fintype.card_pos_iff.mpr ⟨i⟩)
  change delta (assembled boundaryCentral family weights) (.inl b) (.inl (u i)) A≤_
  linarith

theorem construction_spoke_le [Nonempty I] (v : Hub I) (j : Index I)
    (A : Finset (Hub I⊕Index I)) (hj : Sum.inr j∉A) :
    delta construction (.inl v) (.inr j) A≤(dilation (Fintype.card I) : ℝ) := by
  rw [construction,delta_assembled_spoke _ _ _ _ _ _ hj]
  cases j with
  | inl ε =>
    simp only [weights,one_mul,family]
    apply (module_cover_le ε v (hubs A)).trans
    exact_mod_cast two_mul_le_dilation (Fintype.card I) (by have h:=Fintype.card_pos (α:=I);omega)
  | inr i =>
    simp only [weights,family]
    have h0:=(balancing_boolean i).values (hubs A)
    have h1:=(balancing_boolean i).values (insert v (hubs A))
    have hb : balancing i (insert v (hubs A))-balancing i (hubs A)≤1:=by
      rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;> linarith
    calc
      _ ≤ (missCount i : ℝ)*1:=mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = (missCount i : ℝ):=mul_one _
      _ ≤ _:=by exact_mod_cast missCount_le_dilation i

theorem construction_delta_le [Nonempty I] (x y : Hub I⊕Index I) (hxy : x≠y)
    (A : Finset (Hub I⊕Index I)) (hx : x∉A) (hy : y∉A) :
    delta construction x y A≤(dilation (Fintype.card I) : ℝ) := by
  have houter (i j : I) (hij : i≠j)
      (hi : Sum.inl (u i)∉A) (hj : Sum.inl (u j)∉A) :
      delta construction (.inl (u i)) (.inl (u j)) A=0 := by
    apply construction_graphical _ _ (by simpa [u] using hij) ?_ A hi hj
    simp [graph,color,u]
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          cases x <;> cases y
          · exact False.elim (hxy rfl)
          · exact construction_ab_le A hx hy
          · rw [delta_comm]
            exact construction_ab_le A hy hx
          · exact False.elim (hxy rfl)
        | inr i =>
          cases x
          · exact construction_ai_le i A hx hy
          · exact construction_bi_le i A hx hy
      | inr i =>
        cases y with
        | inl y =>
          rw [delta_comm]
          cases y
          · exact construction_ai_le i A hy hx
          · exact construction_bi_le i A hy hx
        | inr j =>
          change delta construction (.inl (u i)) (.inl (u j)) A≤_
          rw [houter i j (fun he => hxy (by subst j;rfl)) hx hy]
          exact Nat.cast_nonneg _
    | inr j => exact construction_spoke_le x j A hy
  | inr j =>
    cases y with
    | inl y =>
      rw [delta_comm]
      exact construction_spoke_le y j A hx
    | inr k =>
      rw [construction,delta_assembled_outer _ _ _ j k
        (fun he => hxy (congrArg Sum.inr he)) A hx hy]
      exact Nat.cast_nonneg _

/-- The quantitative part of Theorem8.4: the actual lattice summand uses
precisely the printed dilation, for every positive parameter. -/
theorem exponential_lattice_summand (p : ℕ) (hp : 1≤p) :
    LatticeExtremeAt (twoSingletonGraph p (2^p+p)) (2^p+2*p+1) ((p-1)*2^p+2) := by
  letI : Nonempty (Fin p):=⟨⟨0,hp⟩⟩
  have hh : LatticeExtremeAt (graph (I:=Fin p) (J:=Index (Fin p)))
      (2^p+2*p+1) (dilation p) := by
    refine ⟨construction,construction_normalized,construction_integer,
      construction_extreme,construction_graphical,?_,?_⟩
    · have hd:=construction_fullDimension (I:=Fin p)
      change Module.finrank ℝ (vectorSpan ℝ (basePolytope (construction (I:=Fin p))))=
        Fintype.card (Hub (Fin p)⊕Index (Fin p))-1 at hd
      rw [hd]
      simp only [Hub,Index,Fintype.card_sum,Fintype.card_bool,Fintype.card_fin,Fintype.card_finset]
      have hpow : 0<(2 : ℕ)^p := by positivity
      omega
    · simpa using construction_delta_le (I:=Fin p)
  let e:=graphIso (I:=Fin p) (J:=Index (Fin p))
  have hm : graph (I:=Fin p) (J:=Index (Fin p))≤
      (twoSingletonGraph (Fintype.card (Fin p)) (Fintype.card (Index (Fin p)))).comap e := by
    intro x y hxy
    exact e.map_adj_iff.mpr hxy
  have he:=hh.embed e.toEquiv.toEmbedding hm
  have hcard : (Fintype.card (Fin p),Fintype.card (Index (Fin p)))=(p,2^p+p) := by
    simp [Index]
  exact Eq.mp (congrArg (fun x : ℕ×ℕ =>
    LatticeExtremeAt (twoSingletonGraph x.1 x.2) (2^p+2*p+1) (dilation p)) hcard) he

end GraphicalZonotopes.TwoHub
