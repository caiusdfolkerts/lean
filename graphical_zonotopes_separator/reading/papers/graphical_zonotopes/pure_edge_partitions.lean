module

public import Papers.GraphicalZonotopes.PureColumnRealization
public import Mathlib.Data.Finset.Prod

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

def orderedPair (C : Finset H) (a b : H) (hab : a<b) (ha : a∈C) (hb : b∈C) :
    PairIn C := ⟨⟨(a,b),hab,(SimpleGraph.top_adj _ _).mpr (ne_of_lt hab)⟩,ha,hb⟩

def pairOfNe (C : Finset H) (a b : H) (hab : a≠b) (ha : a∈C) (hb : b∈C) : PairIn C :=
  if h : a<b then orderedPair C a b h ha hb
  else orderedPair C b a (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hab)) hb ha

theorem pairOfNe_endpoints (C : Finset H) (a b : H) (hab : a≠b)
    (ha : a∈C) (hb : b∈C) :
    ((pairOfNe C a b hab ha hb).1.1.1=a ∧ (pairOfNe C a b hab ha hb).1.1.2=b) ∨
    ((pairOfNe C a b hab ha hb).1.1.1=b ∧ (pairOfNe C a b hab ha hb).1.1.2=a) := by
  unfold pairOfNe
  split <;> simp [orderedPair]

theorem starPairs_nonempty (C : Finset H) {a : H} {B : Finset H}
    (ha : a∈C) (hB : B⊆C) (haB : a∉B) (hne : B.Nonempty) :
    (starPairs C a B).Nonempty := by
  obtain ⟨b,hb⟩ := hne
  have hab : a≠b := fun h => haB (h.symm ▸ hb)
  refine ⟨pairOfNe C a b hab ha (hB hb),?_⟩
  rw [mem_starPairs]
  rcases pairOfNe_endpoints C a b hab ha (hB hb) with h | h <;>
    simp [StarPair,h.1,h.2,hb]

def cliquePairsEquiv (C U : Finset H) (hU : U⊆C) :
    ↥(cliquePairs C U) ≃ ↥((U ×ˢ U).filter (fun p : H×H => p.1<p.2)) where
  toFun e := ⟨e.1.1.1,mem_filter.mpr ⟨mem_product.mpr
    (mem_cliquePairs.mp e.2),e.1.1.2.1⟩⟩
  invFun p := ⟨orderedPair C p.1.1 p.1.2 (mem_filter.mp p.2).2
    (hU (mem_product.mp (mem_filter.mp p.2).1).1)
    (hU (mem_product.mp (mem_filter.mp p.2).1).2),
    mem_cliquePairs.mpr (mem_product.mp (mem_filter.mp p.2).1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cliquePairs_card (C U : Finset H) (hU : U⊆C) :
    (cliquePairs C U).card=U.card.choose 2 := by
  have h := Fintype.card_congr (cliquePairsEquiv C U hU)
  simpa only [Fintype.card_coe,Finset.card_product_filter_lt] using h

theorem cliquePairs_nonempty (C U : Finset H) (hU : U⊆C) (hc : 2≤U.card) :
    (cliquePairs C U).Nonempty := by
  apply card_pos.mp
  rw [cliquePairs_card C U hU]
  exact Nat.choose_pos hc

theorem cliquePairs_nonempty_iff (C U : Finset H) (hU : U⊆C) :
    (cliquePairs C U).Nonempty ↔ 2≤U.card := by
  rw [← card_pos,cliquePairs_card C U hU]
  constructor
  · intro h
    exact Nat.choose_ne_zero_iff.mp (ne_of_gt h)
  · exact Nat.choose_pos

theorem starPairs_union (C : Finset H) (a : H) (B D : Finset H) :
    starPairs C a (B∪D)=starPairs C a B∪starPairs C a D := by
  ext e
  simp only [mem_starPairs,StarPair,mem_union]
  tauto

theorem starPairs_disjoint (C : Finset H) (a : H) {B D : Finset H}
    (hBD : Disjoint B D) (haB : a∉B) (haD : a∉D) :
    Disjoint (starPairs C a B) (starPairs C a D) := by
  apply disjoint_left.mpr
  intro e heB heD
  rw [mem_starPairs] at heB heD
  rcases heB with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;>
    rcases heD with ⟨hu',hv'⟩ | ⟨hv',hu'⟩
  · exact disjoint_left.mp hBD hv hv'
  · exact haD (hu ▸ hu')
  · exact haD (hv ▸ hv')
  · exact disjoint_left.mp hBD hu hu'

theorem starPairs_singleton (C : Finset H) {a b : H} (hab : a≠b)
    (ha : a∈C) (hb : b∈C) :
    starPairs C a {b}={pairOfNe C a b hab ha hb} := by
  ext e
  rw [mem_starPairs,mem_singleton]
  have hends := pairOfNe_endpoints C a b hab ha hb
  constructor
  · intro he
    apply Subtype.ext
    apply Subtype.ext
    rcases he with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · have hv' : e.1.1.2=b := mem_singleton.mp hv
      rcases hends with h | h
      · exact Prod.ext (hu.trans h.1.symm) (hv'.trans h.2.symm)
      · have h1 : a<b := hu ▸ hv' ▸ e.1.2.1
        have h2 : b<a := by simpa only [h.1,h.2] using (pairOfNe C a b hab ha hb).1.2.1
        exact False.elim ((not_lt_of_ge h1.le) h2)
    · have hu' : e.1.1.1=b := mem_singleton.mp hu
      rcases hends with h | h
      · have h1 : b<a := hu' ▸ hv ▸ e.1.2.1
        have h2 : a<b := by simpa only [h.1,h.2] using (pairOfNe C a b hab ha hb).1.2.1
        exact False.elim ((not_lt_of_ge h1.le) h2)
      · exact Prod.ext (hu'.trans h.1.symm) (hv.trans h.2.symm)
  · rintro rfl
    rcases hends with h | h <;> simp [StarPair,h.1,h.2]

theorem starPairs_card (C : Finset H) {a : H} {B : Finset H}
    (ha : a∈C) (hB : B⊆C) (haB : a∉B) :
    (starPairs C a B).card=B.card := by
  induction B using Finset.induction_on with
  | empty => simp [starPairs,StarPair]
  | @insert b B hb ih =>
    have hbC : b∈C := hB (mem_insert_self _ _)
    have hBC : B⊆C := fun x hx => hB (mem_insert_of_mem hx)
    have haB' : a∉B := fun h => haB (mem_insert_of_mem h)
    have hab : a≠b := fun h => haB (mem_insert.mpr (Or.inl h))
    rw [← singleton_union,starPairs_union,card_union_of_disjoint
      (starPairs_disjoint C a (disjoint_singleton_left.mpr hb)
        (by simpa only [mem_singleton] using hab) haB'),
      starPairs_singleton C hab ha hbC,card_singleton,ih hBC haB']
    simp [card_insert_of_notMem hb,Nat.add_comm]

theorem cliquePairs_split (C U : Finset H) (a : H) (ha : a∈U) :
    cliquePairs C U=starPairs C a (U.erase a)∪cliquePairs C (U.erase a) := by
  ext e
  simp only [mem_cliquePairs,mem_union,mem_starPairs,StarPair,mem_erase]
  have huv : e.1.1.1≠e.1.1.2 := ne_of_lt e.1.2.1
  constructor
  · rintro ⟨hu,hv⟩
    by_cases hua : e.1.1.1=a
    · exact Or.inl (Or.inl ⟨hua,fun hvA => huv (hua.trans hvA.symm),hv⟩)
    · by_cases hva : e.1.1.2=a
      · exact Or.inl (Or.inr ⟨hva,hua,hu⟩)
      · exact Or.inr ⟨⟨hua,hu⟩,hva,hv⟩
  · rintro ((⟨hua,hva,hv⟩ | ⟨hva,hua,hu⟩) | ⟨⟨hua,hu⟩,hva,hv⟩)
    · exact ⟨hua.symm ▸ ha,hv⟩
    · exact ⟨hu,hva.symm ▸ ha⟩
    · exact ⟨hu,hv⟩

theorem cliquePairs_split_disjoint (C U : Finset H) (a : H) :
    Disjoint (starPairs C a (U.erase a)) (cliquePairs C (U.erase a)) := by
  apply disjoint_left.mpr
  intro e hs hc
  rw [mem_starPairs] at hs
  obtain ⟨hu,hv⟩ := mem_cliquePairs.mp hc
  rcases hs with ⟨he,_⟩ | ⟨he,_⟩
  · exact (mem_erase.mp hu).1 he
  · exact (mem_erase.mp hv).1 he

/-- The allowed pieces are actual partial stars or cliques of pairs. -/
def PureEdgeChunk (C : Finset H) (A : Finset (PairIn C)) : Prop :=
  (∃ a B, a∈C ∧ B⊆C ∧ a∉B ∧ A=starPairs C a B) ∨
  (∃ U, U⊆C ∧ A=cliquePairs C U)

theorem PureEdgeChunk.realizable {C : Finset H} {A : Finset (PairIn C)}
    (hA : PureEdgeChunk C A) (hne : A.Nonempty) : PureRealizable C (pairIndicator A) := by
  rcases hA with ⟨a,B,ha,hB,haB,rfl⟩ | ⟨U,hU,rfl⟩
  · have hb : B.Nonempty := by
      apply card_pos.mp
      rw [← starPairs_card C ha hB haB]
      exact card_pos.mpr hne
    exact pureRealizable_star C ha hB hb haB
  · exact pureRealizable_clique C U hU ((cliquePairs_nonempty_iff C U hU).mp hne)

theorem PureEdgeChunk.split {C : Finset H} {A : Finset (PairIn C)}
    (hA : PureEdgeChunk C A) (hc : 2≤A.card) :
    ∃ B D : Finset (PairIn C), B.Nonempty ∧ D.Nonempty ∧ Disjoint B D ∧
      B∪D=A ∧ PureEdgeChunk C B ∧ PureEdgeChunk C D := by
  rcases hA with ⟨a,U,ha,hU,haU,rfl⟩ | ⟨U,hU,rfl⟩
  · have hUc : 2≤U.card := by rwa [starPairs_card C ha hU haU] at hc
    obtain ⟨b,hb⟩ := card_pos.mp (by omega : 0<U.card)
    have hab : a≠b := fun h => haU (h.symm ▸ hb)
    have hUe : (U.erase b).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem hb]
      omega
    refine ⟨starPairs C a {b},starPairs C a (U.erase b),
      starPairs_nonempty C ha (singleton_subset_iff.mpr (hU hb))
        (by simpa only [mem_singleton] using hab) (singleton_nonempty b),
      starPairs_nonempty C ha (erase_subset _ _ |>.trans hU)
        (fun h => haU (mem_of_mem_erase h)) hUe,
      starPairs_disjoint C a (disjoint_singleton_left.mpr (notMem_erase b U))
        (by simpa only [mem_singleton] using hab) (fun h => haU (mem_of_mem_erase h)),?_,?_,?_⟩
    · rw [← starPairs_union,singleton_union,insert_erase hb]
    · exact Or.inl ⟨a,{b},ha,singleton_subset_iff.mpr (hU hb),
        by simpa only [mem_singleton] using hab,rfl⟩
    · exact Or.inl ⟨a,U.erase b,ha,(erase_subset _ _).trans hU,
        fun h => haU (mem_of_mem_erase h),rfl⟩
  · have hUc : 3≤U.card := by
      rw [cliquePairs_card C U hU] at hc
      by_contra hn
      have hcases : U.card=0 ∨ U.card=1 ∨ U.card=2 := by omega
      rcases hcases with h | h | h <;> norm_num [h,Nat.choose] at hc
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<U.card)
    have he : 2≤(U.erase a).card := by rw [card_erase_of_mem ha]; omega
    have hsub : U.erase a⊆C := (erase_subset _ _).trans hU
    refine ⟨starPairs C a (U.erase a),cliquePairs C (U.erase a),
      starPairs_nonempty C (hU ha) hsub (notMem_erase _ _) (card_pos.mp (by omega)),
      cliquePairs_nonempty C (U.erase a) hsub he,
      cliquePairs_split_disjoint C U a,(cliquePairs_split C U a ha).symm,?_,?_⟩
    · exact Or.inl ⟨a,U.erase a,hU ha,hsub,notMem_erase _ _,rfl⟩
    · exact Or.inr ⟨U.erase a,hsub,rfl⟩

/-- Every intermediate number of independent pure Boolean columns is
available for a clique or partial-star indicator. -/
theorem pureEdgeChunk_partition (C : Finset H) {A : Finset (PairIn C)}
    (hA : PureEdgeChunk C A) (hne : A.Nonempty) {k : ℕ} (hk : 1≤k) (hkA : k≤A.card) :
    ∃ Q : Finpartition A, Q.parts.card=k ∧
      (∀ B : Q.parts, PureRealizable C (pairIndicator B.1)) ∧
      LinearIndependent ℝ (fun B : Q.parts => pairIndicator B.1) ∧
      (∑ B : Q.parts,pairIndicator B.1)=pairIndicator A := by
  obtain ⟨Q,hQc,hQ⟩ := partition_every_size_of_splitting (PureEdgeChunk C)
    (fun A hA hc => hA.split hc) hne hA k hk hkA
  refine ⟨Q,hQc,fun B => (hQ B.1 B.2).realizable (Q.nonempty_of_mem_parts B.2),
    linearIndependent_partition_indicators Q,?_⟩
  funext e
  simpa only [Finset.sum_apply,pairIndicator] using sum_partition_indicators Q e

end BooleanModule
end GraphicalZonotopes
