module

public import Papers.GraphicalZonotopes.PositiveStarInterpolation

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

private theorem pairIndicator_singleton_eq (C : Finset H) (e : PairIn C) :
    pairIndicator {e}=(fun f => if f=e then (1 : ℝ) else 0) := by
  funext f
  simp only [pairIndicator,mem_singleton]

private theorem pairOfNe_char (C : Finset H) (a b : H) (hab : a≠b)
    (ha : a∈C) (hb : b∈C) (e : PairIn C) :
    e=pairOfNe C a b hab ha hb ↔
      (e.1.1.1=a ∧ e.1.1.2=b) ∨ (e.1.1.2=a ∧ e.1.1.1=b) := by
  have h := congrArg (fun A : Finset (PairIn C) => e∈A)
    (starPairs_singleton C hab ha hb)
  simpa only [mem_starPairs,StarPair,mem_singleton] using Iff.of_eq h.symm

private theorem pairOfNe_symm (C : Finset H) (a b : H) (hab : a≠b)
    (ha : a∈C) (hb : b∈C) :
    pairOfNe C a b hab ha hb=pairOfNe C b a (Ne.symm hab) hb ha := by
  apply (pairOfNe_char C b a (Ne.symm hab) hb ha _).mpr
  rcases pairOfNe_endpoints C a b hab ha hb with h | h
  · exact Or.inr ⟨h.2,h.1⟩
  · exact Or.inl h

private theorem pairOfNe_other_eq (C : Finset H) (a b c : H) (hab : a≠b)
    (hac : a≠c) (ha : a∈C) (hb : b∈C) (hc : c∈C)
    (h : pairOfNe C a b hab ha hb=pairOfNe C a c hac ha hc) : b=c := by
  have hi := (pairOfNe_char C a b hab ha hb _).mp rfl
  have hj := (pairOfNe_char C a c hac ha hc _).mp h
  rcases hi with ⟨hia,hi⟩ | ⟨hia,hi⟩ <;> rcases hj with ⟨hja,hj⟩ | ⟨hja,hj⟩
  · exact hi.symm.trans hj
  · exact False.elim (hac (hia.symm.trans hj))
  · exact False.elim (hac (hia.symm.trans hj))
  · exact hi.symm.trans hj

private theorem pureRealizable_pair_sum (C : Finset H) (b u v : H)
    (hbu : b≠u) (hbv : b≠v) (huv : u≠v)
    (hb : b∈C) (hu : u∈C) (hv : v∈C) :
    PureRealizable C (pairIndicator {pairOfNe C b u hbu hb hu}+
      pairIndicator {pairOfNe C b v hbv hb hv}) := by
  have he : pairIndicator {pairOfNe C b u hbu hb hu}+
      pairIndicator {pairOfNe C b v hbv hb hv}=
      pairIndicator (starPairs C b {u,v}) := by
    rw [← starPairs_singleton C hbu hb hu,← starPairs_singleton C hbv hb hv]
    have hs : ({u,v} : Finset H)={u}∪{v} := by simp
    rw [hs,starPairs_union]
    have hd := starPairs_disjoint C b (B:={u}) (D:={v}) (disjoint_singleton_left.mpr
      (by simpa only [mem_singleton] using huv))
      (by simpa only [mem_singleton] using hbu)
      (by simpa only [mem_singleton] using hbv)
    funext e
    by_cases he1 : e∈starPairs C b {u} <;> by_cases he2 : e∈starPairs C b {v}
    · exact False.elim (disjoint_left.mp hd he1 he2)
    all_goals simp [pairIndicator,he1,he2]
  rw [he]
  apply pureRealizable_star C (a:=b) (B:={u,v}) hb
  · exact insert_subset_iff.mpr ⟨hu,singleton_subset_iff.mpr hv⟩
  · exact insert_nonempty _ _
  · intro h
    rcases mem_insert.mp h with h | h
    · exact hbu h
    · exact hbv (mem_singleton.mp h)

private theorem pivotPositive_unique_owner {E I : Type*} [DecidableEq E]
    [Fintype I] [DecidableEq I] (seed : I → E) (D : Finset E)
    (owner : D → I) (hinj : Function.Injective owner) (d : D) :
    pivotPositive seed D owner (owner d)=
      (fun e => if e=seed (owner d) then (1 : ℝ) else 0)+
      (fun e => if e=d.1 then (1 : ℝ) else 0) := by
  funext e
  simp only [pivotPositive,Pi.add_apply]
  congr 1
  by_cases he : e∈D
  · rw [dite_eq_left he]
    have hh : owner ⟨e,he⟩=owner d ↔ e=d.1 := by
      rw [hinj.eq_iff]
      exact Subtype.ext_iff
    simp only [hh]
  · have hn : e≠d.1 := fun h => he (h.symm ▸ d.2)
    simp [he,hn]

private theorem pivotPositive_no_owner {E I : Type*} [DecidableEq E]
    [Fintype I] [DecidableEq I] (seed : I → E) (D : Finset E)
    (owner : D → I) (i : I) (h : ¬∃ d,owner d=i) :
    pivotPositive seed D owner i=fun e => if e=seed i then (1 : ℝ) else 0 := by
  funext e
  unfold pivotPositive
  by_cases he : e∈D
  · have hn : owner ⟨e,he⟩≠i := fun hh => h ⟨⟨e,he⟩,hh⟩
    simp [he,hn]
  · simp [he]

private theorem extraTip_exists (C : Finset H) (a q : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) (d : D) :
    ∃ b : (C.erase a).erase q,
      d.1=pairOfNe C a b.1 (Ne.symm (mem_erase.mp (mem_of_mem_erase b.2)).1)
        ha (mem_of_mem_erase (mem_of_mem_erase b.2)) := by
  rcases mem_starPairs.mp (hD d.2) with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · refine ⟨⟨d.1.1.1.2,hv⟩,?_⟩
    exact (pairOfNe_char C _ _ _ _ _ _).mpr (Or.inl ⟨hu,rfl⟩)
  · refine ⟨⟨d.1.1.1.1,hu⟩,?_⟩
    exact (pairOfNe_char C _ _ _ _ _ _).mpr (Or.inr ⟨hv,rfl⟩)

private def extraTip (C : Finset H) (a q : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) (d : D) :=
  Classical.choose (extraTip_exists C a q ha D hD d)

private theorem extraTip_spec (C : Finset H) (a q : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) (d : D) :
    d.1=pairOfNe C a (extraTip C a q ha D hD d).1
      (Ne.symm (mem_erase.mp (mem_of_mem_erase (extraTip C a q ha D hD d).2)).1)
      ha (mem_of_mem_erase (mem_of_mem_erase (extraTip C a q ha D hD d).2)) :=
  Classical.choose_spec (extraTip_exists C a q ha D hD d)

private def cliqueOwner (C : Finset H) (a q : H) (ha : a∈C) (hq : q∈C.erase a)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q))
    (d : D) : cliquePairs C (C.erase a) :=
  let b := extraTip C a q ha D hD d
  ⟨pairOfNe C q b.1 (Ne.symm (mem_erase.mp b.2).1)
    (mem_of_mem_erase hq) (mem_of_mem_erase (mem_of_mem_erase b.2)),by
    rw [mem_cliquePairs]
    rcases pairOfNe_endpoints C q b.1 (Ne.symm (mem_erase.mp b.2).1)
      (mem_of_mem_erase hq) (mem_of_mem_erase (mem_of_mem_erase b.2)) with h | h
    · exact ⟨h.1.symm ▸ hq,h.2.symm ▸ mem_of_mem_erase b.2⟩
    · exact ⟨h.1.symm ▸ mem_of_mem_erase b.2,h.2.symm ▸ hq⟩⟩

private theorem cliqueOwner_injective (C : Finset H) (a q : H)
    (ha : a∈C) (hq : q∈C.erase a) (D : Finset (PairIn C))
    (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    Function.Injective (cliqueOwner C a q ha hq D hD) := by
  intro d e h
  let b := extraTip C a q ha D hD d
  let c := extraTip C a q ha D hD e
  have hh := pairOfNe_other_eq C q b.1 c.1
    (Ne.symm (mem_erase.mp b.2).1) (Ne.symm (mem_erase.mp c.2).1)
    (mem_of_mem_erase hq) (mem_of_mem_erase (mem_of_mem_erase b.2))
    (mem_of_mem_erase (mem_of_mem_erase c.2)) (congrArg Subtype.val h)
  have ht : extraTip C a q ha D hD d=extraTip C a q ha D hD e := Subtype.ext hh
  apply Subtype.ext
  rw [extraTip_spec C a q ha D hD d,extraTip_spec C a q ha D hD e,ht]

private theorem cliqueSeed_not_extra (C : Finset H) (a q : H)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    ∀ i : cliquePairs C (C.erase a),i.1∉D := by
  intro i hi
  obtain ⟨hu,hv⟩ := mem_cliquePairs.mp i.2
  rcases mem_starPairs.mp (hD hi) with ⟨hh,_⟩ | ⟨hh,_⟩
  · exact (mem_erase.mp hu).1 hh
  · exact (mem_erase.mp hv).1 hh

private theorem cliquePivot_realizable (C : Finset H) (hC : 3≤C.card)
    (a q : H) (ha : a∈C) (hq : q∈C.erase a) (D : Finset (PairIn C))
    (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    ∀ j : cliquePairs C (C.erase a) ⊕ D,
      PureRealizable C (pivotColumns Subtype.val D (cliqueOwner C a q ha hq D hD) j) := by
  intro j
  cases j with
  | inl i =>
    by_cases hi : ∃ d,cliqueOwner C a q ha hq D hD d=i
    · obtain ⟨d,rfl⟩ := hi
      change PureRealizable C (pivotPositive _ _ _ _)
      rw [pivotPositive_unique_owner Subtype.val D _
        (cliqueOwner_injective C a q ha hq D hD) d]
      let b := extraTip C a q ha D hD d
      have hbq : b.1≠q := (mem_erase.mp b.2).1
      have hba : b.1≠a := (mem_erase.mp (mem_of_mem_erase b.2)).1
      have hbC : b.1∈C := mem_of_mem_erase (mem_of_mem_erase b.2)
      have hqC : q∈C := mem_of_mem_erase hq
      have hqa : q≠a := (mem_erase.mp hq).1
      have he1 : (cliqueOwner C a q ha hq D hD d).1=
          pairOfNe C b.1 q hbq hbC hqC := pairOfNe_symm C q b.1 (Ne.symm hbq) hqC hbC
      have he2 : d.1=pairOfNe C b.1 a hba hbC ha :=
        (extraTip_spec C a q ha D hD d).trans (pairOfNe_symm C a b.1 (Ne.symm hba) ha hbC)
      simp only [he1,he2]
      have hp := pureRealizable_pair_sum C b.1 q a hbq hba hqa hbC hqC ha
      rw [pairIndicator_singleton_eq,pairIndicator_singleton_eq] at hp
      exact hp
    · change PureRealizable C (pivotPositive _ _ _ _)
      rw [pivotPositive_no_owner Subtype.val D _ i hi]
      have hp := pureRealizable_pair C i.1
      rw [pairIndicator_singleton_eq] at hp
      exact hp
  | inr d =>
    have he : pivotColumns (fun i : cliquePairs C (C.erase a) => i.1) D
        (cliqueOwner C a q ha hq D hD) (Sum.inr d)=-pairIndicator {d.1} := by
      funext e
      by_cases h : e=d.1 <;> simp [pivotColumns,pairIndicator,h]
    rw [he]
    exact pureRealizable_negative_pair C hC d.1

private theorem cliquePivot_sum (C : Finset H) (a q : H)
    (ha : a∈C) (hq : q∈C.erase a) (D : Finset (PairIn C))
    (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    (∑ j : cliquePairs C (C.erase a) ⊕ D,
      pivotColumns Subtype.val D (cliqueOwner C a q ha hq D hD) j)=
      pairIndicator (cliquePairs C (C.erase a)) := by
  rw [pivotColumns_sum]
  funext e
  by_cases he : e∈cliquePairs C (C.erase a)
  · have heq : ∀ i : cliquePairs C (C.erase a),e=i.1 ↔ i=⟨e,he⟩ :=
      fun i => ⟨fun h => Subtype.ext h.symm,fun h => congrArg Subtype.val h.symm⟩
    simp [heq,pairIndicator,he]
  · have hn : ∀ i : cliquePairs C (C.erase a),e≠i.1 := fun i h => he (h.symm ▸ i.2)
    simp [hn,pairIndicator,he]

/-- The upper range of the negative-star interpolation. The initial clique
on the other hubs is extended using distinct seed pairs incident with `q`;
the reference pair `aq` is never activated. -/
theorem negative_star_large_interpolation (C : Finset H) (hC : 3≤C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : (C.card-1).choose 2≤k)
    (hkC : k≤C.card.choose 2-1) :
    Nonempty (PureDecomposition C (-blockClass C (starVector C a)) k) := by
  classical
  have hecard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hsub : C.erase a⊆C := erase_subset _ _
  have hchoose : C.card.choose 2=(C.card-1).choose 2+(C.card-1) := by
    have h := Nat.choose_succ_succ (C.card-1) 1
    have hs : C.card-1+1=C.card := by omega
    simpa only [Nat.succ_eq_add_one,hs,Nat.choose_one_right,Nat.add_comm] using h
  obtain ⟨q,hq⟩ := card_pos.mp (show 0<(C.erase a).card by omega)
  have hecard2 : ((C.erase a).erase q).card=C.card-2 := by
    rw [card_erase_of_mem hq,hecard]
    omega
  have hsub2 : (C.erase a).erase q⊆C := (erase_subset _ _).trans hsub
  have hn : a∉(C.erase a).erase q := fun h => (notMem_erase a C) (mem_of_mem_erase h)
  have hcapacity : k-(C.card-1).choose 2≤(starPairs C a ((C.erase a).erase q)).card := by
    rw [starPairs_card C ha hsub2 hn,hecard2]
    omega
  obtain ⟨D,hD,hDc⟩ := exists_subset_card_eq hcapacity
  let owner := cliqueOwner C a q ha hq D hD
  let seed := fun i : cliquePairs C (C.erase a) => i.1
  let x := pivotColumns seed D owner
  let e₀ := pairOfNe C a q (Ne.symm (mem_erase.mp hq).1) ha (mem_of_mem_erase hq)
  have hnotseed : ∀ i : cliquePairs C (C.erase a),e₀≠seed i := by
    intro i hi
    obtain ⟨hu,hv⟩ := mem_cliquePairs.mp i.2
    have hends := pairOfNe_endpoints C a q (Ne.symm (mem_erase.mp hq).1) ha (mem_of_mem_erase hq)
    rcases hends with hh | hh
    · exact (mem_erase.mp hu).1 ((congrArg (fun e : PairIn C => e.1.1.1) hi).symm.trans hh.1)
    · exact (mem_erase.mp hv).1 ((congrArg (fun e : PairIn C => e.1.1.2) hi).symm.trans hh.2)
  have heD : e₀∉D := by
    intro h
    have hs := mem_starPairs.mp (hD h)
    have hends := (pairOfNe_char C a q (Ne.symm (mem_erase.mp hq).1) ha (mem_of_mem_erase hq) e₀).mp rfl
    rcases hs with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;> rcases hends with hh | hh
    · exact (mem_erase.mp hv).1 hh.2
    · exact (mem_erase.mp hq).1 (hh.2.symm.trans hu)
    · exact (mem_erase.mp hq).1 (hh.2.symm.trans hv)
    · exact (mem_erase.mp hu).1 hh.2
  apply pureDecomposition_of_vectors x (cliquePivot_realizable C hC a q ha hq D hD)
    (blockClass_linearIndependent_of_reference C e₀ x
      (pivotColumns_linearIndependent seed Subtype.val_injective D owner
        (cliqueSeed_not_extra C a q D hD))
      (pivotColumns_zero_at seed D owner e₀ heD hnotseed)) _ _
  · rw [← map_sum,cliquePivot_sum C a q ha hq D hD]
    exact clique_without_vertex_class C a
  · simp only [Fintype.card_sum,Fintype.card_coe,cliquePairs_card C (C.erase a) hsub,
      hecard,hDc]
    omega

/-- The negative half of Lemma 7.7, with every count through the entire
block dimension and actual Boolean realizations. -/
theorem negative_star_interpolation (C : Finset H) (hC : 3≤C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤k) (hkC : k≤C.card.choose 2-1) :
    Nonempty (PureDecomposition C (-blockClass C (starVector C a)) k) := by
  by_cases h : k≤(C.card-1).choose 2
  · exact negative_star_small_interpolation C hC a ha hk h
  · exact negative_star_large_interpolation C hC a ha (by omega) hkC

end BooleanModule
end GraphicalZonotopes
