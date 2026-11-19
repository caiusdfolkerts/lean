module

public import Papers.GraphicalZonotopes.TwoHubRestriction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The cube partition hypotheses are constructed for every needed size in
`CubePartition.exists_proper_card`. They are not assumptions of the final
complete multipartite graph theorem. -/
structure PartitionData (I : Type*) [Fintype I] [DecidableEq I] where
  cells : Finset (Cell I)
  valid : CubePartition.Valid cells
  proper : ∀ C∈cells,C.fixed.Nonempty
  uses : CubePartition.UsesZero cells univ

namespace PartitionData
variable (P : PartitionData I)

abbrev Index := P.cells⊕I

def misses (C : P.cells) (i : I) : Prop := i∈C.1.fixed ∧ i∉C.1.ones
instance (C : P.cells) (i : I) : Decidable (P.misses C i) :=
  inferInstanceAs (Decidable (i∈C.1.fixed ∧ i∉C.1.ones))

def missCount (i : I) : ℕ := (univ.filter (fun C : P.cells => P.misses C i)).card

def family : P.Index → SetFunction (Hub I)
  | .inl C => C.1.function
  | .inr i => balancing i

def weights : P.Index → ℝ
  | .inl _ => 1
  | .inr i => (P.missCount i : ℝ)

def boundary : SetFunction (Hub I) :=
  assembled (pair 0 0 1) (fun i X => if true∈X then (P.missCount i : ℝ) else 0) (fun _ => 1)

def construction : SetFunction (Hub I⊕P.Index) := assembled P.boundary P.family P.weights

theorem missCount_pos (i : I) : 0<P.missCount i := by
  obtain ⟨C,hC,hi,hio⟩:=P.uses i (mem_univ i)
  exact card_pos.mpr ⟨⟨C,hC⟩,mem_filter.mpr ⟨mem_univ _,hi,hio⟩⟩

theorem weights_pos (j : P.Index) : 0<P.weights j := by
  cases j with
  | inl C => norm_num [weights]
  | inr i => simpa [weights] using (Nat.cast_pos.mpr (P.missCount_pos i) : (0 : ℝ)<_)

theorem family_empty (j : P.Index) : P.family j ∅=0 := by
  cases j with
  | inl C => exact C.1.empty
  | inr i => exact (balancing_boolean i).empty

theorem family_monotone (j : P.Index) (v : Hub I) (S : Finset (Hub I)) :
    0≤P.family j (insert v S)-P.family j S := by
  cases j with
  | inl C => exact C.1.cover_nonnegative (P.proper C.1 C.2) v S
  | inr i => exact sub_nonneg.mpr ((balancing_boolean i).monotone (subset_insert v S))

theorem family_privateRigid (j : P.Index) : PrivateRigid (P.family j) := by
  cases j with
  | inl C => exact C.1.privateRigid (P.proper C.1 C.2)
  | inr i => exact (balancing_boolean i).privateRigid

theorem family_ai_response (j : P.Index) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : negativeResponse (P.family j) a (u i) S=0 := by
  cases j with
  | inl C => exact C.1.ai_response i S ha hi
  | inr k => exact balancing_ai_response k i S ha hi

theorem response_sum_ab (t : P.Index → ℝ) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) (C : P.cells) (hC : C.1.Matches (outers S)) :
    (∑ j : P.Index,t j*negativeResponse (P.family j) a b S)=t (.inl C) := by
  rw [Fintype.sum_sum_type]
  simp only [family,Cell.ab_response _ _ ha hb,balancing_ab_response _ _ ha hb,
    mul_zero,sum_const_zero,add_zero,mul_ite,mul_one]
  rw [sum_eq_single C]
  · simp [hC]
  · intro D hD hDC
    have hm : ¬D.1.Matches (outers S) := by
      intro hm
      exact hDC (Subtype.ext (P.valid.unique D.2 C.2 hm hC))
    simp [hm]
  · simp

theorem response_sum_ai (t : P.Index → ℝ) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    (∑ j : P.Index,t j*negativeResponse (P.family j) a (u i) S)=0 := by
  simp only [P.family_ai_response _ _ _ ha hi,mul_zero,sum_const_zero]

theorem response_sum_bi (t : P.Index → ℝ) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (∑ j : P.Index,t j*negativeResponse (P.family j) b (u i) S)=
      if a∈S then t (.inr i) else ∑ C : P.cells,if P.misses C i then t (.inl C) else 0 := by
  rw [Fintype.sum_sum_type]
  simp only [family,Cell.bi_response _ _ _ hb hi,balancing_bi_response _ _ _ hb hi]
  by_cases ha : a∈S
  · simp [ha]
  · simp only [ha,ite_false,ite_self,mul_ite,mul_one,mul_zero,sum_const_zero,add_zero,misses]
    <;> rfl

theorem family_outer_zero (j : P.Index) : OuterZero (P.family j) := by
  cases j with
  | inl C => exact C.1.outer_zero
  | inr i => exact balancing_outer_zero i

theorem family_outer_response (j : P.Index) (i k : I) (hik : i≠k)
    (S : Finset (Hub I)) (hi : u i∉S) (hk : u k∉S) :
    negativeResponse (P.family j) (u i) (u k) S=0 := by
  rw [negativeResponse]
  have hz : delta (P.family j) (u i) (u k) S=0 := P.family_outer_zero j i k hik S hi hk
  rw [hz,neg_zero,max_self]

theorem compatible_ai_zero {h : SetFunction (Hub I)} {t : P.Index → ℝ}
    (hc : Compatible h P.family t) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : delta h a (u i) S=0 := by
  rw [hc a (u i) (by simp [a,u]) S ha hi,P.response_sum_ai _ _ _ ha hi]

theorem compatible_ab_constant {h : SetFunction (Hub I)} {t : P.Index → ℝ}
    (hc : Compatible h P.family t) (Y : Finset I) :
    delta h a b (outerSet Y)=delta h a b ∅ := by
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert i Y hi ih =>
    rw [outerSet_insert]
    have hh:=delta_insert_difference h a b (u i) (outerSet Y)
    have hz0:=P.compatible_ai_zero hc i (outerSet Y) (by simp [a]) (by simpa [u] using hi)
    have hz1:=P.compatible_ai_zero hc i (insert b (outerSet Y))
      (by simp [a,b]) (by simpa [u,b] using hi)
    rw [hz0,hz1] at hh
    change delta h a b (insert (u i) (outerSet Y))=delta h a b ∅
    rw [←ih]
    linarith

theorem unique_relation : UniqueIntegrableRelation P.family P.weights := by
  intro t ht
  obtain ⟨h,hn,hc⟩:=ht
  let c:=delta h a b ∅
  have hm (C : P.cells) : t (.inl C)=c := by
    have he:=hc a b (by simp [a,b]) (outerSet C.1.ones) (by simp [a]) (by simp [b])
    rw [P.response_sum_ab _ _ (by simp [a]) (by simp [b]) C
      (by
        have hY : outers (outerSet (H:=Bool) C.1.ones)=C.1.ones := by ext i; simp
        rw [hY]
        exact C.1.matches_ones)] at he
    exact he.symm.trans (P.compatible_ab_constant hc C.1.ones)
  have hb (i : I) : t (.inr i)=(P.missCount i : ℝ)*c := by
    have hz0:=P.compatible_ai_zero hc i (∅ : Finset (Hub I)) (by simp) (by simp)
    have hz1:=P.compatible_ai_zero hc i {b} (by simp [a,b]) (by simp [b,u])
    have hd:=delta_insert_difference h (u i) b a ∅
    rw [delta_comm (u i) b,delta_comm (u i) b,delta_comm (u i) a,delta_comm (u i) a] at hd
    simp only [insert_empty_eq] at hd
    rw [hz0,hz1] at hd
    have h0:=hc b (u i) (by simp [b,u]) ∅ (by simp) (by simp)
    have h1:=hc b (u i) (by simp [b,u]) {a} (by simp [a,b]) (by simp [a,u])
    rw [P.response_sum_bi _ _ _ (by simp) (by simp)] at h0
    rw [P.response_sum_bi _ _ _ (by simp [a,b]) (by simp [a,u])] at h1
    simp only [notMem_empty,not_false_eq_true,if_false,mem_singleton,ite_true] at h0 h1
    have hs : (∑ C : P.cells,if P.misses C i then t (.inl C) else 0)=(P.missCount i : ℝ)*c := by
      simp_rw [hm]
      rw [←sum_filter]
      simp only [sum_const,nsmul_eq_mul,missCount]
    rw [hs] at h0
    linarith
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl C => simpa [weights] using hm C
  | inr i => simpa [weights,mul_comm] using hb i

theorem boundary_normalized : TranslationNormalized P.boundary := by
  apply assembled_normalized_general
  · constructor
    · simp [Normalized,pair]
    · intro v
      cases v <;> simp [pair]
  · intro i
    simp

theorem boundary_ab (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    delta P.boundary a b S=1 := by
  have hh : hubs S=∅ := by
    ext v
    cases v <;> simp_all [a,b]
  rw [boundary,a,b,delta_assembled_hubs,hh,delta_pair]
  have hd (i : I) : delta (fun X : Finset Bool => if true∈X then (P.missCount i : ℝ) else 0)
      false true ∅=0 := by simp [delta]
  simp only [hd,ite_self,mul_zero,sum_const_zero,add_zero]

theorem boundary_ai (i : I) (S : Finset (Hub I)) (hi : u i∉S) :
    delta P.boundary a (u i) S=0 := by
  rw [boundary,a,u,delta_assembled_spoke _ _ _ _ _ _ hi]
  simp

theorem boundary_bi (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
    delta P.boundary b (u i) S=(P.missCount i : ℝ) := by
  have hx : true∉hubs S := by simpa [b] using hb
  rw [boundary,b,u,delta_assembled_spoke _ _ _ _ _ _ hi]
  simp [hx]

theorem boundary_outer : OuterZero P.boundary := by
  intro i j hij S hi hj
  exact delta_assembled_outer _ _ _ i j hij S hi hj

theorem missing_sum (i : I) :
    (∑ C : P.cells,if P.misses C i then (1 : ℝ) else 0)=(P.missCount i : ℝ) := by
  rw [←sum_filter]
  simp [missCount]

/-- All conditioning sets are treated, including those outside a cell's
fixed coordinates. -/
theorem central_compatible : Compatible P.boundary P.family P.weights := by
  have hab (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
      delta P.boundary a b S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) a b S := by
    obtain ⟨C,hC,hu⟩:=P.valid (outers S)
    rw [P.boundary_ab S ha hb,P.response_sum_ab _ _ ha hb ⟨C,hC.1⟩ hC.2]
    rfl
  have hai (i : I) (S : Finset (Hub I)) (ha : a∉S) (hi : u i∉S) :
      delta P.boundary a (u i) S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) a (u i) S := by
    rw [P.boundary_ai i S hi,P.response_sum_ai _ _ _ ha hi]
  have hbi (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
      delta P.boundary b (u i) S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) b (u i) S := by
    rw [P.boundary_bi i S hb hi,P.response_sum_bi _ _ _ hb hi]
    by_cases ha : a∈S
    · simp [ha,weights]
    · simp only [ha,ite_false,weights,P.missing_sum]
  have hij (i j : I) (hne : i≠j) (S : Finset (Hub I)) (hi : u i∉S) (hj : u j∉S) :
      delta P.boundary (u i) (u j) S=
        ∑ k : P.Index,P.weights k*negativeResponse (P.family k) (u i) (u j) S := by
    have hz : delta P.boundary (u i) (u j) S=0 := P.boundary_outer i j hne S hi hj
    rw [hz]
    simp only [P.family_outer_response _ _ _ hne S hi hj,mul_zero,sum_const_zero]
  have swap (x y : Hub I) (S : Finset (Hub I))
      (h : delta P.boundary x y S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) x y S) :
      delta P.boundary y x S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) y x S := by
    simpa only [negativeResponse,delta_comm y x] using h
  intro x y hxy S hx hy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x <;> cases y
      · exact False.elim (hxy rfl)
      · exact hab S hx hy
      · exact swap a b S (hab S hy hx)
      · exact False.elim (hxy rfl)
    | inr i =>
      cases x
      · exact hai i S hx hy
      · exact hbi i S hx hy
  | inr i =>
    cases y with
    | inl y =>
      cases y
      · exact swap a (u i) S (hai i S hy hx)
      · exact swap b (u i) S (hbi i S hy hx)
    | inr j => exact hij i j (fun he => hxy (congrArg Sum.inr he)) S hx hy

theorem construction_normalized : TranslationNormalized P.construction :=
  assembled_normalized_general P.boundary_normalized P.family P.family_empty P.weights

theorem construction_supermodular : Supermodular P.construction :=
  assembled_supermodular_general P.boundary P.family P.family_monotone P.weights
    (fun j => (P.weights_pos j).le) P.central_compatible

theorem construction_extreme [Nonempty I] : ExtremeSupermodular P.construction := by
  apply positive_circuit_extreme_general P.boundary_normalized P.family_empty P.family_monotone
    P.family_privateRigid (fun j => (P.weights_pos j).le) _ P.central_compatible P.unique_relation
  refine ⟨Sum.inr (Classical.choice ‹Nonempty I›),univ,?_⟩
  simp only [family,weights,(balancing_boolean _).full,mul_one]
  exact ne_of_gt (Nat.cast_pos.mpr (P.missCount_pos _) : (0 : ℝ)<_)

end PartitionData
end GraphicalZonotopes.TwoHub
