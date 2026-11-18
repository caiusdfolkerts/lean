module

public import Papers.GraphicalZonotopes.SignedPairBases
public import Papers.GraphicalZonotopes.NegativeStarInterpolation

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

theorem starVector_eq_zero_of_notMem (C : Finset H) {a : H} (ha : a∉C) :
    starVector C a=0 := by
  funext e
  have hu : a≠e.1.1.1 := fun h => ha (h.symm ▸ e.2.1)
  have hv : a≠e.1.1.2 := fun h => ha (h.symm ▸ e.2.2)
  simp only [starVector_eq,hu,hv,false_or,ite_false,Pi.zero_apply]

def PureDecomposition.toWeightedBlock {C : Finset H} {v : ResponseQuotient H} {r : ℕ}
    (P : PureDecomposition C v r) (M : ℤ) (hM : 1≤M) : WeightedPureBlock C M v r := by
  classical
  choose x hx using P.block_supported
  exact {
    column := x
    realizable := fun j => ⟨P.functions j,P.monotone_boolean j,P.essential j,P.ignored j,hx j⟩
    weight := fun _ => 1
    positive := fun _ => by norm_num
    bounded := fun _ => hM
    independent := by simpa only [← hx] using P.independent
    weighted_sum := by simpa only [Int.cast_one,one_smul,← hx] using P.sum_eq
  }

def twoAnchorTarget (C : Finset H) (a b : H) : ResponseQuotient H :=
  -((-1 : ℝ)^(C.card-3) • blockClass C (starVector C a+starVector C b))

theorem twoAnchorTarget_symm (C : Finset H) (a b : H) :
    twoAnchorTarget C a b=twoAnchorTarget C b a := by rw [twoAnchorTarget,twoAnchorTarget,add_comm]

theorem one_anchor_pure_block (C : Finset H) (hC : 3≤C.card)
    {a b : H} (ha : a∈C) (hb : b∉C) {k : ℕ} (hk : 1≤k)
    (hkC : k≤C.card.choose 2-1) :
    Nonempty (WeightedPureBlock C 2 (twoAnchorTarget C a b) k) := by
  have hb0 := starVector_eq_zero_of_notMem C hb
  rcases neg_one_pow_eq_or ℝ (C.card-3) with h | h
  · obtain ⟨P⟩ := negative_star_interpolation C hC a ha hk hkC
    refine ⟨?_⟩
    have hp := P.toWeightedBlock 2 (by norm_num)
    simpa only [twoAnchorTarget,hb0,add_zero,h,one_smul] using hp
  · obtain ⟨P⟩ := positive_star_interpolation C hC a ha hk hkC
    refine ⟨?_⟩
    have hp := P.toWeightedBlock 2 (by norm_num)
    simpa only [twoAnchorTarget,hb0,add_zero,h,neg_one_smul,neg_neg] using hp

theorem pair_contains_two_iff (C : Finset H) {a b : H} (hab : a<b)
    (ha : a∈C) (hb : b∈C) (e : PairIn C) :
    ((a=e.1.1.1 ∨ a=e.1.1.2) ∧ (b=e.1.1.1 ∨ b=e.1.1.2)) ↔
      e=orderedPair C a b hab ha hb := by
  constructor
  · rintro ⟨(hae | hae),(hbe | hbe)⟩
    · exact False.elim ((ne_of_lt hab) (hae.trans hbe.symm))
    · apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hae.symm hbe.symm
    · have hbad : b<a := by simpa only [← hae,← hbe] using e.1.2.1
      exact False.elim ((not_lt_of_ge hab.le) hbad)
    · exact False.elim ((ne_of_lt hab) (hae.trans hbe.symm))
  · rintro rfl
    exact ⟨Or.inl rfl,Or.inr rfl⟩

def twoAnchorPairWeight (C : Finset H) (a b : H) (e : PairIn C) : ℤ :=
  2-((if a=e.1.1.1 ∨ a=e.1.1.2 then 1 else 0)+
    (if b=e.1.1.1 ∨ b=e.1.1.2 then 1 else 0))

theorem twoAnchorPairWeight_zero (C : Finset H) {a b : H} (hab : a<b)
    (ha : a∈C) (hb : b∈C) :
    twoAnchorPairWeight C a b (orderedPair C a b hab ha hb)=0 := by
  simp [twoAnchorPairWeight,orderedPair]

theorem twoAnchorPairWeight_positive (C : Finset H) {a b : H} (hab : a<b)
    (ha : a∈C) (hb : b∈C) (e : PairIn C)
    (he : e≠orderedPair C a b hab ha hb) : 0<twoAnchorPairWeight C a b e := by
  have hn := mt (pair_contains_two_iff C hab ha hb e).mp he
  by_cases hA : a=e.1.1.1 ∨ a=e.1.1.2 <;>
    by_cases hB : b=e.1.1.1 ∨ b=e.1.1.2 <;> simp_all [twoAnchorPairWeight]

theorem twoAnchorPairWeight_bounded (C : Finset H) (a b : H) (e : PairIn C) :
    twoAnchorPairWeight C a b e≤2 := by
  unfold twoAnchorPairWeight
  split <;> split <;> norm_num

theorem twoAnchorPairWeight_vector (C : Finset H) (a b : H) :
    (fun e => (twoAnchorPairWeight C a b e : ℝ))=
      (fun _ : PairIn C => (2 : ℝ))-(starVector C a+starVector C b) := by
  funext e
  simp only [twoAnchorPairWeight,Int.cast_sub,Int.cast_ofNat,Int.cast_add,
    Pi.sub_apply,Pi.add_apply,starVector_eq]
  by_cases hA : a=e.1.1.1 ∨ a=e.1.1.2 <;>
    by_cases hB : b=e.1.1.1 ∨ b=e.1.1.2 <;> simp [hA,hB]

/-- Every double-anchor block other than the single connector is filled to
its full quotient dimension with positive integral weights one or two. -/
theorem two_anchor_full_pure_block (C : Finset H) (hC : 3≤C.card)
    {a b : H} (hab : a<b) (ha : a∈C) (hb : b∈C) :
    Nonempty (WeightedPureBlock C 2 (twoAnchorTarget C a b) (C.card.choose 2-1)) := by
  let e₀ := orderedPair C a b hab ha hb
  let ε : ℝ := (-1)^(C.card-3)
  let P := signed_pair_basis C hC e₀ ε (neg_one_pow_eq_or ℝ (C.card-3))
    (twoAnchorPairWeight C a b) (twoAnchorPairWeight_zero C hab ha hb)
    (fun e he => twoAnchorPairWeight_positive C hab ha hb e he) 2
    (fun e _ => twoAnchorPairWeight_bounded C a b e)
  have hz : blockClass C (fun _ : PairIn C => (2 : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨2,fun _ => rfl⟩
  have hv : blockClass C (ε • (fun e => (twoAnchorPairWeight C a b e : ℝ)))=
      twoAnchorTarget C a b := by
    rw [twoAnchorPairWeight_vector,map_smul,map_sub,hz,zero_sub,smul_neg]
    rfl
  exact ⟨hv ▸ P⟩

end BooleanModule
end GraphicalZonotopes
