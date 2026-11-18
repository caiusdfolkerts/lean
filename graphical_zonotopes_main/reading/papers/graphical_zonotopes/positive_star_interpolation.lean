module

public import Papers.GraphicalZonotopes.PureDecompositions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

private def starSeed (C : Finset H) (a : H) (ha : a∈C) (i : C.erase a) : PairIn C :=
  pairOfNe C a i.1 (Ne.symm (mem_erase.mp i.2).1) ha (mem_of_mem_erase i.2)

private theorem starSeed_eq_iff (C : Finset H) (a : H) (ha : a∈C)
    (i : C.erase a) (e : PairIn C) :
    e=starSeed C a ha i ↔
      (e.1.1.1=a ∧ e.1.1.2=i.1) ∨ (e.1.1.2=a ∧ e.1.1.1=i.1) := by
  have h := congrArg (fun A : Finset (PairIn C) => e∈A)
    (starPairs_singleton C (Ne.symm (mem_erase.mp i.2).1) ha (mem_of_mem_erase i.2))
  simpa only [mem_starPairs,StarPair,mem_singleton,starSeed] using Iff.of_eq h.symm

private theorem starSeed_injective (C : Finset H) (a : H) (ha : a∈C) :
    Function.Injective (starSeed C a ha) := by
  intro i j hij
  have hi := (starSeed_eq_iff C a ha i (starSeed C a ha i)).mp rfl
  have hj := (starSeed_eq_iff C a ha j (starSeed C a ha i)).mp hij
  apply Subtype.ext
  rcases hi with ⟨hia,hi⟩ | ⟨hia,hi⟩ <;> rcases hj with ⟨hja,hj⟩ | ⟨hja,hj⟩
  · exact hi.symm.trans hj
  · exact False.elim ((mem_erase.mp j.2).1 (hj.symm.trans hia))
  · exact False.elim ((mem_erase.mp j.2).1 (hj.symm.trans hia))
  · exact hi.symm.trans hj

private theorem starSeed_range (C : Finset H) (a : H) (ha : a∈C) (e : PairIn C) :
    e∈starPairs C a (C.erase a) ↔ ∃ i : C.erase a,e=starSeed C a ha i := by
  rw [mem_starPairs]
  constructor
  · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
    · exact ⟨⟨e.1.1.2,hv⟩,(starSeed_eq_iff C a ha _ e).mpr (Or.inl ⟨hu,rfl⟩)⟩
    · exact ⟨⟨e.1.1.1,hu⟩,(starSeed_eq_iff C a ha _ e).mpr (Or.inr ⟨hv,rfl⟩)⟩
  · rintro ⟨i,hi⟩
    rcases (starSeed_eq_iff C a ha i e).mp hi with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact Or.inl ⟨hu,hv.symm ▸ i.2⟩
    · exact Or.inr ⟨hv,hu.symm ▸ i.2⟩

private theorem starSeed_not_extra (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆cliquePairs C (C.erase a)) :
    ∀ i,starSeed C a ha i∉D := by
  intro i h
  obtain ⟨hu,hv⟩ := mem_cliquePairs.mp (hD h)
  rcases (starSeed_eq_iff C a ha i (starSeed C a ha i)).mp rfl with hh | hh
  · exact (mem_erase.mp hu).1 hh.1
  · exact (mem_erase.mp hv).1 hh.1

private def starOwner (C : Finset H) (a : H) (D : Finset (PairIn C))
    (hD : D⊆cliquePairs C (C.erase a)) (d : D) : C.erase a :=
  ⟨d.1.1.1.1,(mem_cliquePairs.mp (hD d.2)).1⟩

private def starOutNeighbors (C : Finset H) (a : H) (D : Finset (PairIn C))
    (i : C.erase a) : Finset H :=
  insert a ((D.filter (fun e => e.1.1.1=i.1)).image (fun e => e.1.1.2))

private theorem starOutNeighbors_subset (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (i : C.erase a) : starOutNeighbors C a D i⊆C := by
  intro b hb
  rcases mem_insert.mp hb with rfl | hb
  · exact ha
  · obtain ⟨e,he,rfl⟩ := mem_image.mp hb
    exact e.2.2

private theorem starOutNeighbors_ne (C : Finset H) (a : H)
    (D : Finset (PairIn C)) (i : C.erase a) : i.1∉starOutNeighbors C a D i := by
  intro h
  rcases mem_insert.mp h with h | h
  · exact (mem_erase.mp i.2).1 h
  · obtain ⟨e,he,hi⟩ := mem_image.mp h
    have he' := (mem_filter.mp he).2
    exact (ne_of_lt e.1.2.1) (he'.trans hi.symm)

private theorem starOutNeighbors_characterization (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆cliquePairs C (C.erase a))
    (i : C.erase a) (e : PairIn C) :
    StarPair i.1 (starOutNeighbors C a D i) e.1.1.1 e.1.1.2 ↔
      e=starSeed C a ha i ∨ ∃ h : e∈D,starOwner C a D hD ⟨e,h⟩=i := by
  constructor
  · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
    · rcases mem_insert.mp hv with hv | hv
      · exact Or.inl ((starSeed_eq_iff C a ha i e).mpr (Or.inr ⟨hv,hu⟩))
      · obtain ⟨d,hd,hv⟩ := mem_image.mp hv
        have hdu := (mem_filter.mp hd).2
        have he : e=d := by
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext (hu.trans hdu.symm) hv.symm
        have heD : e∈D := he.symm ▸ (mem_filter.mp hd).1
        exact Or.inr ⟨heD,Subtype.ext hu⟩
    · rcases mem_insert.mp hu with hu | hu
      · exact Or.inl ((starSeed_eq_iff C a ha i e).mpr (Or.inl ⟨hu,hv⟩))
      · obtain ⟨d,hd,hu⟩ := mem_image.mp hu
        have hdu := (mem_filter.mp hd).2
        have hlt : e.1.1.2<e.1.1.1 := by
          simpa only [hdu,hu,hv] using d.1.2.1
        exact False.elim ((not_lt_of_ge e.1.2.1.le) hlt)
  · rintro (h | ⟨heD,howner⟩)
    · rcases (starSeed_eq_iff C a ha i e).mp h with ⟨hu,hv⟩ | ⟨hv,hu⟩
      · exact Or.inr ⟨hv,hu.symm ▸ mem_insert_self _ _⟩
      · exact Or.inl ⟨hu,hv.symm ▸ mem_insert_self _ _⟩
    · have hu : e.1.1.1=i.1 := congrArg Subtype.val howner
      exact Or.inl ⟨hu,mem_insert_of_mem (mem_image.mpr
        ⟨e,mem_filter.mpr ⟨heD,hu⟩,rfl⟩)⟩

private theorem starPivot_realizable (C : Finset H) (hC : 3≤C.card)
    (a : H) (ha : a∈C) (D : Finset (PairIn C))
    (hD : D⊆cliquePairs C (C.erase a)) :
    ∀ j : C.erase a ⊕ D, PureRealizable C
      (pivotColumns (starSeed C a ha) D (starOwner C a D hD) j) := by
  intro j
  cases j with
  | inl i =>
    have he : pivotColumns (starSeed C a ha) D (starOwner C a D hD) (Sum.inl i)=
        pairIndicator (starPairs C i.1 (starOutNeighbors C a D i)) := by
      funext e
      change pivotPositive _ _ _ i e=_
      simp only [pairIndicator,mem_starPairs,starOutNeighbors_characterization C a ha D hD i e]
      unfold pivotPositive
      by_cases hs : e=starSeed C a ha i
      · have hn : e∉D := hs.symm ▸ starSeed_not_extra C a ha D hD i
        have hn' := starSeed_not_extra C a ha D hD i
        simp [hs,hn']
      · by_cases heD : e∈D
        · simp only [hs,ite_false,dite_eq_left heD,zero_add,false_or]
          congr 1
          apply propext
          constructor
          · exact fun h => ⟨heD,h⟩
          · exact fun ⟨_,h⟩ => h
        · simp [hs,heD]
    rw [he]
    exact pureRealizable_star C (mem_of_mem_erase i.2)
      (starOutNeighbors_subset C a ha D i) ⟨a,mem_insert_self _ _⟩
      (starOutNeighbors_ne C a D i)
  | inr d =>
    have he : pivotColumns (starSeed C a ha) D (starOwner C a D hD) (Sum.inr d)=
        -pairIndicator {d.1} := by
      funext e
      by_cases h : e=d.1 <;> simp [pivotColumns,pairIndicator,h]
    rw [he]
    exact pureRealizable_negative_pair C hC d.1

private theorem starPivot_sum (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆cliquePairs C (C.erase a)) :
    (∑ j : C.erase a ⊕ D,pivotColumns (starSeed C a ha) D (starOwner C a D hD) j)=
      starVector C a := by
  rw [pivotColumns_sum]
  funext e
  change (∑ i : C.erase a,if e=starSeed C a ha i then (1 : ℝ) else 0)=
    if e∈starPairs C a (C.erase a) then 1 else 0
  by_cases he : e∈starPairs C a (C.erase a)
  · obtain ⟨i,rfl⟩ := (starSeed_range C a ha e).mp he
    have hinj := starSeed_injective C a ha
    simp only [hinj.eq_iff,ite_eq_left he]
    simp
  · have hn : ∀ i : C.erase a,e≠starSeed C a ha i :=
      fun i h => he ((starSeed_range C a ha e).mpr ⟨i,h⟩)
    simp [he,hn]

/-- The second range in the positive-star interpolation. New pairs are
inserted into an actual partial-star column and canceled by a negative pure
pair. Unique seed pairs and the omitted reference pair prove independence. -/
theorem positive_star_large_interpolation (C : Finset H) (hC : 3≤C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : C.card-1≤k) (hkC : k≤C.card.choose 2-1) :
    Nonempty (PureDecomposition C (blockClass C (starVector C a)) k) := by
  classical
  have hecard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hsub : C.erase a⊆C := erase_subset _ _
  have hchoose : C.card.choose 2=(C.card-1).choose 2+(C.card-1) := by
    have h := Nat.choose_succ_succ (C.card-1) 1
    have hs : C.card-1+1=C.card := by omega
    simpa only [Nat.succ_eq_add_one,hs,Nat.choose_one_right,Nat.add_comm] using h
  obtain ⟨e₀,he₀⟩ := cliquePairs_nonempty C (C.erase a) hsub (by omega)
  have hcapacity : k-(C.card-1)≤((cliquePairs C (C.erase a)).erase e₀).card := by
    rw [card_erase_of_mem he₀,cliquePairs_card C (C.erase a) hsub,hecard]
    omega
  obtain ⟨D,hD,hDc⟩ := exists_subset_card_eq hcapacity
  have hD' : D⊆cliquePairs C (C.erase a) := hD.trans (erase_subset _ _)
  let seed := starSeed C a ha
  let owner := starOwner C a D hD'
  let x := pivotColumns seed D owner
  have hreal : ∀ j,PureRealizable C (x j) := starPivot_realizable C hC a ha D hD'
  have hind : LinearIndependent ℝ x := pivotColumns_linearIndependent seed
    (starSeed_injective C a ha) D owner (starSeed_not_extra C a ha D hD')
  have hzero : ∀ j,x j e₀=0 := by
    apply pivotColumns_zero_at seed D owner e₀
    · exact fun h => (mem_erase.mp (hD h)).1 rfl
    · intro i he
      have hm := he.symm ▸ he₀
      exact starSeed_not_extra C a ha (cliquePairs C (C.erase a)) (Subset.refl _) i hm
  apply pureDecomposition_of_vectors x hreal
    (blockClass_linearIndependent_of_reference C e₀ x hind hzero) _ _
  · rw [← map_sum]
    exact congrArg (blockClass C) (starPivot_sum C a ha D hD')
  · simp only [Fintype.card_sum,Fintype.card_coe,hecard,hDc]
    omega

/-- The positive half of Lemma 7.7, with every intermediate count and the
actual response quotient. -/
theorem positive_star_interpolation (C : Finset H) (hC : 3≤C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤k) (hkC : k≤C.card.choose 2-1) :
    Nonempty (PureDecomposition C (blockClass C (starVector C a)) k) := by
  by_cases h : k≤C.card-1
  · exact positive_star_small_interpolation C hC a ha hk h
  · exact positive_star_large_interpolation C hC a ha (by omega) hkC

end BooleanModule
end GraphicalZonotopes
