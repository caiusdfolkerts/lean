module

public import Papers.GraphicalZonotopes.TwoHubPartitionGeometry
public import Papers.GraphicalZonotopes.TwoHubPartitionCost
public import Papers.GraphicalZonotopes.TwoHubCellBounds
public import Papers.GraphicalZonotopes.TwoHubDilation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace GraphicalZonotopes.TwoHub.PartitionData
open Finset BooleanModule SetFunctionEmbedding
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (P : PartitionData I)

theorem missCount_sum (i : I) :
    (P.missCount i : ℝ)=∑ C : P.cells,if P.misses C i then 1 else 0 := by
  simp [missCount]

theorem partitionDilation_cast :
    (P.partitionDilation : ℝ)=(P.totalDepth : ℝ)-(P.cells.card : ℝ)+2 := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) P.sum_pred_depth_add_card
  simp only [Nat.cast_add] at h
  unfold partitionDilation
  rw [Nat.cast_add]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem positive_ab_sum (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    (∑ C : P.cells,max 0 (delta C.1.function a b S))=
      (∑ C : P.cells,(distance C.1.assignment (C.1.pull (outers S)) : ℝ))-
        (P.cells.card : ℝ)+1 := by
  have he (C : P.cells) : max 0 (delta C.1.function a b S)=
      (distance C.1.assignment (C.1.pull (outers S)) : ℝ)-1+
        negativeResponse C.1.function a b S := by
    rw [max_zero_eq_add_negative]
    change delta C.1.function a b S+negativeResponse C.1.function a b S=_
    rw [C.1.ab_delta_distance S ha hb]
  obtain ⟨C,hC,hu⟩ := P.valid (outers S)
  have hr := P.response_sum_ab (fun _ => 1) S ha hb ⟨C,hC.1⟩ hC.2
  rw [Fintype.sum_sum_type] at hr
  simp only [family,balancing_ab_response _ _ ha hb,one_mul,sum_const_zero,add_zero] at hr
  simp_rw [he]
  rw [sum_add_distrib,sum_sub_distrib,hr]
  simp

theorem distances_and_balancing_le_depth (Y : Finset I) :
    (∑ C : P.cells,(distance C.1.assignment (C.1.pull Y) : ℝ))+
      ∑ i : I,(P.missCount i : ℝ)*(if i∈Y then 0 else 1)≤(P.totalDepth : ℝ) := by
  have h := sum_le_sum (fun C (_ : C∈(univ : Finset P.cells)) =>
    C.1.distance_missing_le_fixed Y)
  rw [sum_add_distrib] at h
  simp_rw [P.missCount_sum,sum_mul]
  rw [sum_comm]
  simpa only [misses,totalDepth,Nat.cast_sum] using h

theorem positive_balancing_ab_sum (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    (∑ i : I,(P.missCount i : ℝ)*max 0 (delta (balancing i) a b S))=
      ∑ i : I,(P.missCount i : ℝ)*(if i∈outers S then 0 else 1) := by
  apply sum_congr rfl
  intro i hi
  rw [balancing_ab_delta i S ha hb]
  by_cases hu : u i∈S <;> simp [hu,show (i∈outers S ↔ u i∈S) from by simp [u]]

theorem construction_ab_le (A : Finset (Hub I⊕P.Index))
    (ha : Sum.inl (a : Hub I)∉A) (hb : Sum.inl (b : Hub I)∉A) :
    delta P.construction (.inl a) (.inl b) A≤(P.partitionDilation : ℝ) := by
  have ha' : a∉hubs A := by simpa using ha
  have hb' : b∉hubs A := by simpa using hb
  have h := assembled_hubs_le P.boundary P.family P.weights
    (fun j => (P.weights_pos j).le) a b A
  rw [P.boundary_ab _ ha' hb',Fintype.sum_sum_type] at h
  simp only [family,weights,one_mul] at h
  rw [P.positive_ab_sum _ ha' hb',P.positive_balancing_ab_sum _ ha' hb'] at h
  have hbnd := P.distances_and_balancing_le_depth (outers (hubs A))
  rw [P.partitionDilation_cast]
  change delta (assembled P.boundary P.family P.weights) (.inl a) (.inl b) A≤_
  linarith

theorem positive_balancing_ai_sum (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    (∑ j : I,(P.missCount j : ℝ)*max 0 (delta (balancing j) a (u i) S))=
      (P.missCount i : ℝ)*(if b∈S then 0 else 1) := by
  have he (j : I) : max 0 (delta (balancing j) a (u i) S)=
      if j=i then (if b∈S then 0 else 1) else 0 := by
    rw [balancing_ai_delta j i S ha hi]
    split_ifs <;> norm_num
  simp_rw [he]
  by_cases hb : b∈S <;> simp [hb]

theorem positive_balancing_bi_sum (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (∑ j : I,(P.missCount j : ℝ)*max 0 (delta (balancing j) b (u i) S))=0 := by
  apply sum_eq_zero
  intro j hj
  rw [balancing_bi_delta j i S hb hi]
  split_ifs <;> norm_num

theorem positive_ai_sum_le_fixCount (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    (∑ C : P.cells,max 0 (delta C.1.function a (u i) S))+
      (P.missCount i : ℝ)*(if b∈S then 0 else 1)≤(P.fixCount i : ℝ) := by
  rw [P.missCount_sum,sum_mul,←sum_add_distrib]
  have h := sum_le_sum (fun C (_ : C∈(univ : Finset P.cells)) =>
    C.1.ai_positive_plus_missing i S ha hi)
  simpa only [misses,sum_boole,fixCount] using h

theorem positive_bi_sum_le_fixCount (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (P.missCount i : ℝ)+(∑ C : P.cells,max 0 (delta C.1.function b (u i) S))≤
      (P.fixCount i : ℝ) := by
  rw [P.missCount_sum,←sum_add_distrib]
  have h := sum_le_sum (fun C (_ : C∈(univ : Finset P.cells)) =>
    C.1.bi_positive_plus_missing i S hb hi)
  simpa only [misses,sum_boole,fixCount] using h

theorem construction_ai_le (i : I) (A : Finset (Hub I⊕P.Index))
    (ha : Sum.inl (a : Hub I)∉A) (hi : Sum.inl (u i)∉A) :
    delta P.construction (.inl a) (.inl (u i)) A≤(P.partitionDilation : ℝ) := by
  have ha' : a∉hubs A := by simpa using ha
  have hi' : u i∉hubs A := by simpa using hi
  have h := assembled_hubs_le P.boundary P.family P.weights
    (fun j => (P.weights_pos j).le) a (u i) A
  rw [P.boundary_ai _ _ hi',Fintype.sum_sum_type,zero_add] at h
  simp only [family,weights,one_mul] at h
  rw [P.positive_balancing_ai_sum _ _ ha' hi'] at h
  have hmain := P.positive_ai_sum_le_fixCount i (hubs A) ha' hi'
  have hcount : (P.fixCount i : ℝ)≤(P.partitionDilation : ℝ) := by
    exact_mod_cast P.fixCount_le_partitionDilation i
  exact h.trans (hmain.trans hcount)

theorem construction_bi_le (i : I) (A : Finset (Hub I⊕P.Index))
    (hb : Sum.inl (b : Hub I)∉A) (hi : Sum.inl (u i)∉A) :
    delta P.construction (.inl b) (.inl (u i)) A≤(P.partitionDilation : ℝ) := by
  have hb' : b∉hubs A := by simpa using hb
  have hi' : u i∉hubs A := by simpa using hi
  have h := assembled_hubs_le P.boundary P.family P.weights
    (fun j => (P.weights_pos j).le) b (u i) A
  rw [P.boundary_bi _ _ hb' hi',Fintype.sum_sum_type] at h
  simp only [family,weights,one_mul] at h
  rw [P.positive_balancing_bi_sum _ _ hb' hi',add_zero] at h
  have hmain := P.positive_bi_sum_le_fixCount i (hubs A) hb' hi'
  have hcount : (P.fixCount i : ℝ)≤(P.partitionDilation : ℝ) := by
    exact_mod_cast P.fixCount_le_partitionDilation i
  exact h.trans (hmain.trans hcount)

theorem construction_spoke_le (v : Hub I) (j : P.Index)
    (A : Finset (Hub I⊕P.Index)) (hj : Sum.inr j∉A) :
    delta P.construction (.inl v) (.inr j) A≤(P.partitionDilation : ℝ) := by
  rw [construction,delta_assembled_spoke _ _ _ _ _ _ hj]
  cases j with
  | inl C =>
    simp only [weights,one_mul,family]
    apply (C.1.cover_le_fixed_card (P.proper C.1 C.2) v (hubs A)).trans
    exact_mod_cast P.fixed_card_le_partitionDilation C
  | inr i =>
    simp only [weights,family]
    have h0 := (balancing_boolean i).values (hubs A)
    have h1 := (balancing_boolean i).values (insert v (hubs A))
    have hb : balancing i (insert v (hubs A))-balancing i (hubs A)≤1 := by
      rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;> linarith
    calc
      _ ≤ (P.missCount i : ℝ)*1 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = (P.missCount i : ℝ) := mul_one _
      _ ≤ _ := by exact_mod_cast P.missCount_le_partitionDilation i

theorem construction_delta_le (x y : Hub I⊕P.Index) (hxy : x≠y)
    (A : Finset (Hub I⊕P.Index)) (hx : x∉A) (hy : y∉A) :
    delta P.construction x y A≤(P.partitionDilation : ℝ) := by
  have houter (i j : I) (hij : i≠j)
      (hi : Sum.inl (u i)∉A) (hj : Sum.inl (u j)∉A) :
      delta P.construction (.inl (u i)) (.inl (u j)) A=0 := by
    apply P.construction_graphical _ _ (by simpa [u] using hij) ?_ A hi hj
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
          · exact P.construction_ab_le A hx hy
          · rw [delta_comm]
            exact P.construction_ab_le A hy hx
          · exact False.elim (hxy rfl)
        | inr i =>
          cases x
          · exact P.construction_ai_le i A hx hy
          · exact P.construction_bi_le i A hx hy
      | inr i =>
        cases y with
        | inl y =>
          rw [delta_comm]
          cases y
          · exact P.construction_ai_le i A hy hx
          · exact P.construction_bi_le i A hy hx
        | inr j =>
          change delta P.construction (.inl (u i)) (.inl (u j)) A≤_
          rw [houter i j (fun he => hxy (by subst j; rfl)) hx hy]
          exact Nat.cast_nonneg _
    | inr j => exact P.construction_spoke_le x j A hy
  | inr j =>
    cases y with
    | inl y =>
      rw [delta_comm]
      exact P.construction_spoke_le y j A hx
    | inr k =>
      rw [construction,delta_assembled_outer _ _ _ j k
        (fun he => hxy (congrArg Sum.inr he)) A hx hy]
      exact Nat.cast_nonneg _

theorem lattice_extreme_at [Nonempty I] :
    LatticeExtremeAt (graph (I:=I) (J:=P.Index))
      (P.cells.card+2*Fintype.card I+1) (P.totalDepth-P.cells.card+2) := by
  rw [←P.partitionDilation_eq]
  refine ⟨P.construction,P.construction_normalized,P.construction_integer,
    P.construction_extreme,P.construction_graphical,?_,P.construction_delta_le⟩
  have hd := P.construction_fullDimension
  change Module.finrank ℝ (vectorSpan ℝ (basePolytope P.construction))=
    Fintype.card (Hub I⊕P.Index)-1 at hd
  rw [hd]
  simp only [Hub,Index,Fintype.card_sum,Fintype.card_bool,Fintype.card_coe]
  omega

end GraphicalZonotopes.TwoHub.PartitionData
