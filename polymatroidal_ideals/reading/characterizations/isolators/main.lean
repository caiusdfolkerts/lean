import Characterizations.Isolators.Sharp

/-! # Propositions 4.7 and 4.10 in the actual localized polynomial rings -/
noncomputable section
set_option maxHeartbeats 700000
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

@[simp] lemma indicatorExponent_support (A : Finset V) : (indicatorExponent A).support = A := by
  ext i
  simp [Finsupp.mem_support_iff, indicatorExponent_apply]

/-- Proposition 4.10: exact degree, all local generation tests, the unique bad
localization, and the sharp first nonlinear position in genuine derived Tor. -/
theorem exists_sharp_isolator (U : Finset V) (hm : 2 ≤ U.card) (d : ℕ) (hd : 2 ≤ d)
    (hk : Uᶜ.card ≤ d-2) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B d ∧ LocallyEquigenerated B ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) ∧
      Equigenerated (localFamily B U) (d-Uᶜ.card) ∧
      FirstNonlinear (k := k) (localFamily B U) (d-Uᶜ.card)
        (min (d-1-Uᶜ.card) (U.card-1)) := by
  let e := min (d-Uᶜ.card) U.card
  have he2 : 2 ≤ e := le_min (by omega) hm
  have heU : e ≤ U.card := min_le_right _ _
  have hed : e+Uᶜ.card ≤ d := by have := min_le_left (d-Uᶜ.card) U.card; dsimp [e]; omega
  obtain ⟨A, hAU, hAe⟩ := Finset.exists_subset_card_eq heU
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
  let q := indicatorExponent A
  let c : Exponent V := Finsupp.single a (d-(e+Uᶜ.card))
  let B := translatedFamily c (pureIsolator U q)
  have hq : q.support ⊆ U := by simpa [q] using hAU
  have hqs : q.support.card = e := by simpa [q] using hAe
  have hqd : q.degree = e := by simpa [q] using hAe
  have hcd : c.degree = d-(e+Uᶜ.card) := Finsupp.degree_single _ _
  have hcU : c.support ⊆ U := by
    intro i hi
    have hai : a = i := by
      by_contra hn
      have hz : c i = 0 := by simp [c, Finsupp.single_apply, hn, Ne.symm hn]
      exact Finsupp.mem_support_iff.mp hi hz
    simpa [← hai] using ha
  have hlocaldeg : q.degree+(restrictExponent U c).degree = d-Uᶜ.card := by
    rw [hqd, restrict_degree_eq U c hcU, hcd]
    omega
  have hposition : q.support.card-1 = min (d-1-Uᶜ.card) (U.card-1) := by
    rw [hqs]
    dsimp [e]
    by_cases h : d-Uᶜ.card ≤ U.card
    · rw [min_eq_left h, min_eq_left (by omega)]
      omega
    · rw [min_eq_right (by omega), min_eq_right (by omega)]
  refine ⟨B, translatedFamily_nonempty (pureIsolator_nonempty U q hq (by omega)) c,
    ?_, translatedFamily_locallyEquigenerated (pureIsolator_locallyEquigenerated U q hq (by omega)) c,
    ?_, ?_, ?_⟩
  · have hh := translatedFamily_equigenerated (pureIsolator_degree U q) c
    have heq : q.degree+Uᶜ.card+c.degree = d := by rw [hqd, hcd]; omega
    simpa only [heq] using hh
  · intro R
    rw [monomialLocalization_eq]
    exact shiftedPure_unique_bad U q c hq (by omega) R
  · simpa only [hlocaldeg] using shiftedPure_local_at_degree U q c hq (by omega)
  · simpa only [hlocaldeg, hposition] using shiftedPure_first (k := k) U q c hq (by omega)

/-- Proposition 4.7(i), including U=E: the smallest exhibited pure degree is k+2. -/
theorem exists_pure_isolator (U : Finset V) (hm : 2 ≤ U.card) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B (Uᶜ.card+2) ∧ LocallyEquigenerated B ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
  obtain ⟨B, hB, hd, hl, hu, _⟩ := exists_sharp_isolator (k := k) U hm (Uᶜ.card+2) (by omega) (by omega)
  exact ⟨B, hB, hd, hl, hu⟩

/-- Proposition 4.7(ii): one mixed-degree localization, all other localizations
having actual linear free resolutions, at the smaller degree k+1. -/
theorem exists_mixed_isolator (U : Finset V) (hm : 2 ≤ U.card) (hk : 1 ≤ Uᶜ.card) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B (Uᶜ.card+1) ∧
      (¬ ∃ e, Equigenerated (localFamily B U) e) ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < U.card by omega)
  have hT : Uᶜ.Nonempty := Finset.card_pos.mp (by omega)
  let B := pureIsolator U (Finsupp.single a 1)
  have hne : B.Nonempty := by
    exact ⟨_, purePower_mem Uᶜ _ (mixed_removed_support U a ha hT) a (by simpa using ha)⟩
  refine ⟨B, hne, ?_, ?_, ?_⟩
  · simpa [Nat.add_comm] using pureIsolator_degree U (Finsupp.single a 1)
  · rw [show localFamily B U = mixedCore (⟨a, ha⟩ : U) from mixedIsolator_local_at U a ha hT]
    exact mixedCore_not_equigenerated (⟨a, ha⟩ : U) ⟨b, hb⟩
      (fun he => hab (congrArg Subtype.val he))
  · intro R
    rw [monomialLocalization_eq]
    exact mixedIsolator_unique_bad U a b ha hb hab hT R

/-- The outer-band generation test of Proposition 4.10 is individually necessary. -/
theorem exists_outer_band_isolator (U : Finset V) (hm : 2 ≤ U.card) (d : ℕ)
    (hd : 2 ≤ d) (hk : Uᶜ.card = d-1) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B d ∧
      (¬ ∃ e, Equigenerated (localFamily B U) e) ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
  have hpos : 1 ≤ Uᶜ.card := by omega
  obtain ⟨B, hB, he, hbad, hgood⟩ := exists_mixed_isolator (k := k) U hm hpos
  have hdeg : Uᶜ.card+1 = d := by omega
  exact ⟨B, hB, hdeg ▸ he, hbad, hgood⟩

end Characterizations.Isolators
