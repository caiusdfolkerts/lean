import Characterizations.ExactCoverage

/-! # The full degree-sensitive sufficient coverage theorem -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def OrderPattern (o : VariableOrder V) (C : Finset V) (i q j : V) : Prop :=
  o i < o j ∧ o q < o j ∧ ∀ t ∈ C, o t < o i ∧ o t < o q

def CoversPatterns (s : ℕ) (F : Set (VariableOrder V)) : Prop :=
  ∀ i q j, i ≠ q → i ≠ j → q ≠ j → ∀ C : Finset V,
    C ⊆ tripleCap i q j → C.card = s → ∃ o ∈ F, OrderPattern o C i q j

theorem card_positive_except_le_degree {a : Exponent V} {S : Finset V} {j : V}
    (hjS : j ∉ S) (hj : 0 < a j) (hS : ∀ x ∈ S, 0 < a x) : S.card + 1 ≤ a.degree := by
  have hones : onesOn (insert j S) ≤ a := by
    intro x
    by_cases hx : x ∈ insert j S
    · have hh : 0 < a x := by
        rcases mem_insert.mp hx with rfl | hx
        · exact hj
        · exact hS x hx
      simpa [hx] using (show 1 ≤ a x by omega)
    · simp [hx]
  have hh := degree_mono hones
  simpa [hjS] using hh

theorem singletonExchange_of_degree_patterns {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (hd : d ≤ Fintype.card V - 2) (F : Set (VariableOrder V))
    (hF : CoversPatterns (d - 1) F)
    (hL : ∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) : SingletonExchange B := by
  intro a ha b hb i huniq j hj
  have hi : b i < a i := (huniq i).mpr rfl
  have hij : i ≠ j := by intro he; subst j; omega
  let C₀ := (pairCap i j).filter (fun x => 0 < b x)
  have hC₀pair : C₀ ⊆ pairCap i j := filter_subset _ _
  have hC₀card : C₀.card ≤ d - 1 := by
    have hh := card_positive_except_le_degree (a := b) (S := C₀) (j := j)
      (by simp [C₀]) (by omega) (fun x hx => (mem_filter.mp hx).2)
    rw [hB b hb] at hh
    omega
  have hpaircard : (pairCap i j).card = Fintype.card V - 2 := by
    rw [pairCap, card_sdiff_of_subset (subset_univ _)]
    simp [hij]
  obtain ⟨C, hC₀C, hCpair, hCcard⟩ := exists_subsuperset_card_eq hC₀pair hC₀card
    (show d - 1 ≤ (pairCap i j).card by omega)
  have hCproper : C.card < (pairCap i j).card := by
    have hdpos : 0 < d := by
      have hh := card_positive_except_le_degree (a := b) (S := ∅) (j := j)
        (by simp) (by omega) (by simp)
      rw [hB b hb] at hh
      simp only [card_empty, zero_add] at hh
      omega
    omega
  obtain ⟨q, hqpair, hqC⟩ := exists_mem_notMem_of_card_lt_card hCproper
  obtain ⟨hqi, hqj⟩ := (mem_pairCap _ _ _).mp hqpair
  have hCcap : C ⊆ tripleCap i q j := by
    intro x hx
    obtain ⟨hxi, hxj⟩ := (mem_pairCap _ _ _).mp (hCpair hx)
    exact (mem_tripleCap _ _ _ _).mpr ⟨hxi, fun he => hqC (he ▸ hx), hxj⟩
  obtain ⟨o, ho, hpattern⟩ := hF i q j hqi.symm hij hqj C hCcap hCcard
  have hbzero (x : V) (hxi : x ≠ i) (hxj : x ≠ j) (hxC : x ∉ C) : b x = 0 := by
    by_contra hn
    apply hxC
    apply hC₀C
    exact mem_filter.mpr ⟨(mem_pairCap _ _ _).mpr ⟨hxi, hxj⟩, by omega⟩
  have hab : variableRevlex o a b := by
    refine ⟨j, hj, ?_⟩
    intro x hx
    have hxi : x ≠ i := by intro he; subst x; exact (not_lt_of_gt hpattern.1) hx
    have hxj : x ≠ j := by intro he; subst x; exact (lt_irrefl _ hx)
    have hxC : x ∉ C := by
      intro hxC
      exact (lt_irrefl _ (hx.trans ((hpattern.2.2 x hxC).1.trans hpattern.1)))
    have hbx := hbzero x hxi hxj hxC
    have hax : a x ≤ b x := by
      by_contra hn
      exact hxi ((huniq x).mp (by omega))
    omega
  obtain ⟨w, hw, hwb, z, hwz, haz⟩ := witness_of_linearQuotients hB.antichain
    (variableRevlex_irrefl o) (hL o ho) a ha b hb hab
  have hzi : z = i := (huniq z).mp haz
  subst z
  obtain ⟨t, hit, ht, hew⟩ := witness_is_exchange hB hw hb hwz
  have horder := (variableRevlex_exchange_iff o b hit.symm ht).mp (hew ▸ hwb)
  have htj : t = j := by
    by_contra htj
    have htC : t ∈ C := hC₀C (mem_filter.mpr ⟨(mem_pairCap _ _ _).mpr ⟨hit.symm, htj⟩, ht⟩)
    exact (not_lt_of_gt (hpattern.2.2 t htC).1) horder
  simpa [hew, htj] using hw


theorem exists_three_distinct (hcard : 3 ≤ Fintype.card V) :
    ∃ i q j : V, i ≠ q ∧ i ≠ j ∧ q ≠ j := by
  let e := (Fintype.equivFin V).symm
  refine ⟨e ⟨0, by omega⟩, e ⟨1, by omega⟩, e ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;>
    intro h <;> have he := congrArg Fin.val (e.injective h) <;> simp at he

theorem CoversPatterns.nonempty {s : ℕ} {F : Set (VariableOrder V)}
    (hF : CoversPatterns s F) (hcard : 3 ≤ Fintype.card V) (hs : s ≤ Fintype.card V - 3) :
    F.Nonempty := by
  obtain ⟨i, q, j, hiq, hij, hqj⟩ := exists_three_distinct hcard
  have hcapcard : (tripleCap i q j).card = Fintype.card V - 3 := by
    rw [tripleCap, card_sdiff_of_subset (subset_univ _)]
    simp [hiq, hij, hqj]
  obtain ⟨C, hC, hc⟩ := exists_subset_card_eq (show s ≤ (tripleCap i q j).card by omega)
  obtain ⟨o, ho, _⟩ := hF i q j hiq hij hqj C hC hc
  exact ⟨o, ho⟩

/-- Theorem 5.4, the full sufficient direction for all degrees and variable
numbers in its main range. No condition is imposed on unused variables. -/
theorem exchange_of_degree_coverage {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hcard : 4 ≤ Fintype.card V)
    (F : Set (VariableOrder V)) (hpatterns : CoversPatterns (min (d - 1) (Fintype.card V - 3)) F)
    (hpairs : Fintype.card V - 1 ≤ d → CoversFinalPairs F)
    (hL : ∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) : ExchangeAxiom B := by
  obtain ⟨o₀, ho₀⟩ := hpatterns.nonempty (by omega) (Nat.min_le_right _ _)
  have hconn := boxConnected_of_linearQuotients hB (variableRevlex_irrefl o₀)
    (fun {_ _ _} => variableRevlex_trans o₀) (variableRevlex_total o₀) (hL o₀ ho₀)
  have hsingle : SingletonExchange B := by
    by_cases hd : Fintype.card V - 1 ≤ d
    · exact singletonExchange_of_finalPairs hB F (hpairs hd) hL
    · have hd' : d ≤ Fintype.card V - 2 := by omega
      have hmin : min (d - 1) (Fintype.card V - 3) = d - 1 := by omega
      exact singletonExchange_of_degree_patterns hB hd' F (hmin ▸ hpatterns) hL
  by_contra hfail
  obtain ⟨c, u, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij, hiq,
    hp, hj, he, hni, hnq, hnqi, hniq⟩ := four_coordinate_obstruction hB hconn hsingle hfail
  let C₀ := (tripleCap i q j).filter (fun x => 0 < c x)
  have hC₀cap : C₀ ⊆ tripleCap i q j := filter_subset _ _
  have hcapcard : (tripleCap i q j).card = Fintype.card V - 3 := by
    rw [tripleCap, card_sdiff_of_subset (subset_univ _)]
    simp [hiq, hij, hqj]
  have hC₀d : C₀.card ≤ d - 1 := by
    have hh := card_positive_except_le_degree (a := c) (S := C₀) (j := j)
      (by simp [C₀]) hj (fun x hx => (mem_filter.mp hx).2)
    rw [hB c hc] at hh
    omega
  have hC₀card : C₀.card ≤ min (d - 1) (Fintype.card V - 3) :=
    le_min hC₀d (by have hh := card_le_card hC₀cap; omega)
  obtain ⟨C, hC₀C, hCcap, hCcard⟩ := exists_subsuperset_card_eq hC₀cap hC₀card
    (show min (d - 1) (Fintype.card V - 3) ≤ (tripleCap i q j).card by omega)
  obtain ⟨o, ho, hpattern⟩ := hpatterns i q j hiq hij hqj C hCcap hCcard
  have hpC : p ∈ C := hC₀C (mem_filter.mpr
    ⟨(mem_tripleCap _ _ _ _).mpr ⟨hip.symm, hpq, hpj⟩, hp⟩)
  have hpord : o p < o j := (hpattern.2.2 p hpC).1.trans hpattern.1
  subst u
  have huc : variableRevlex o (exchange (exchange c p q) j i) c := by
    refine ⟨j, ?_, ?_⟩
    · simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, if_neg hij.symm,
        ite_true, Nat.sub_zero, Nat.add_zero]
      omega
    · intro x hx
      have hxp : x ≠ p := by intro he; subst x; exact (not_lt_of_gt hpord) hx
      have hxq : x ≠ q := by intro he; subst x; exact (not_lt_of_gt hpattern.2.1) hx
      have hxi : x ≠ i := by intro he; subst x; exact (not_lt_of_gt hpattern.1) hx
      have hxj : x ≠ j := by intro he; subst x; exact (lt_irrefl _ hx)
      simp [hxp, hxq, hxi, hxj]
  obtain ⟨w, hw, hwc, z, hwz, hcz⟩ := witness_of_linearQuotients hB.antichain
    (variableRevlex_irrefl o) (hL o ho) _ hu c hc huc
  have hziq : z = i ∨ z = q := by
    by_contra hz
    push_neg at hz
    simp only [exchange_apply, if_neg hz.1, if_neg hz.2, Nat.add_zero] at hcz
    split_ifs at hcz <;> omega
  obtain ⟨t, hzt, ht, hew⟩ := witness_is_exchange hB hw hc hwz
  have horder : o z < o t :=
    (variableRevlex_exchange_iff o c hzt.symm ht).mp (hew ▸ hwc)
  rcases hziq with rfl | rfl
  · by_cases htj : t = j
    · exact hni (by simpa [hew, htj] using hw)
    by_cases htq : t = q
    · exact hnqi (by simpa [hew, htq] using hw)
    have htC : t ∈ C := hC₀C (mem_filter.mpr
      ⟨(mem_tripleCap _ _ _ _).mpr ⟨hzt.symm, htq, htj⟩, ht⟩)
    exact (not_lt_of_gt (hpattern.2.2 t htC).1) horder
  · by_cases htj : t = j
    · exact hnq (by simpa [hew, htj] using hw)
    by_cases hti : t = i
    · exact hniq (by simpa [hew, hti] using hw)
    have htC : t ∈ C := hC₀C (mem_filter.mpr
      ⟨(mem_tripleCap _ _ _ _).mpr ⟨hti, hzt.symm, htj⟩, ht⟩)
    exact (not_lt_of_gt (hpattern.2.2 t htC).2) horder

end Characterizations
