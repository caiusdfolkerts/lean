import Characterizations.Isolators.Shift
import Characterizations.Resolution.Betti

/-! # Exact sharpness: a prescribed first nonlinear derived-Tor position -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- All earlier homological positions are linear, and the displayed position has
an actual nonzero derived-Tor component in a strictly larger total degree. -/
def FirstNonlinear (B : Family V) (d r : ℕ) : Prop :=
  (∀ i < r, ∀ b, b.degree ≠ d+i → bettiNumber (k := k) B b i = 0) ∧
  ∃ b, d+r < b.degree ∧ 0 < bettiNumber (k := k) B b r

lemma firstNonlinear_not_linear {B : Family V} {d r : ℕ}
    (hBne : B.Nonempty) (hdeg : Equigenerated B d) (hfirst : FirstNonlinear (k := k) B d r) :
    ¬ HasLinearResolution (monomialIdeal k B) := by
  rintro ⟨e, ⟨P⟩⟩
  have he := LinearResolution.equigenerated_of_monomial B hdeg.antichain P
  obtain ⟨b, hb⟩ := hBne
  have hed : e = d := (he b hb).symm.trans (hdeg b hb)
  subst e
  obtain ⟨a, ha, hp⟩ := hfirst.2
  have hz := LinearResolution.bettiNumber_eq_zero_off_linear B hdeg.antichain P a r (Nat.ne_of_gt ha)
  omega

lemma deletedVeronese_shift_first (a c : Exponent V) (ha : 2 ≤ a.support.card) :
    FirstNonlinear (k := k) (translatedFamily c (deletedVeronese a))
      (a.degree+c.degree) (a.support.card-1) := by
  obtain ⟨hzero, hone⟩ := Strands.deletedVeronese_first_nonlinear (k := k) a ha
  constructor
  · intro i hi b hoff
    by_cases hc : c ≤ b
    · have he : b = (b-c)+c := (tsub_add_cancel_of_le hc).symm
      rw [he, bettiNumber_translated]
      apply hzero i hi (b-c)
      intro hd
      apply hoff
      rw [he, map_add, hd]
      omega
    · exact bettiNumber_translated_outside _ _ _ _ hc
  · refine ⟨(a+faceExponent a.support)+c, ?_, ?_⟩
    · rw [map_add, map_add, Strands.degree_faceExponent]
      omega
    · rw [bettiNumber_translated, hone]
      exact Nat.zero_lt_one

lemma restrict_support_card (U : Finset V) (q : Exponent V) (hq : q.support ⊆ U) :
    (restrictExponent U q).support.card = q.support.card := by
  rw [restrictExponent, Finsupp.support_subtypeDomain, Finset.card_subtype]
  rw [Finset.filter_eq_self.mpr hq]

lemma restrict_degree_eq (U : Finset V) (q : Exponent V) (hq : q.support ⊆ U) :
    (restrictExponent U q).degree = q.degree := by
  rw [restrictExponent_degree, Finsupp.degree_eq_sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hiU
  exact Finsupp.notMem_support_iff.mp (fun h => hiU (hq h))

lemma shiftedPure_local_linear (U R : Finset V) (q c : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) (hRU : R ≠ U) :
    HasLinearResolution (monomialIdeal k (localFamily (translatedFamily c (pureIsolator U q)) R)) := by
  rw [localFamily_translated]
  by_cases hUR : U ⊆ R
  · rw [pureIsolator_local_contain U R q hq hsupp hUR]
    refine ⟨_, translated_deletedBounded_linearResolution _ _ _ _ ?_ ?_⟩
    · intro i hi
      exact removedExponent_saturated U q hq i.val ((mem_retainedCaps _ _ _).mp hi)
    · have hex : ∃ i ∈ R, i ∉ U := by
        by_contra hn
        push_neg at hn
        exact hRU (le_antisymm hn hUR)
      obtain ⟨i, hiR, hiU⟩ := hex
      exact ⟨⟨i, hiR⟩, by simp [hiU]⟩
  · rw [pureIsolator_local_omit U R q hsupp hUR]
    have he : translatedFamily (restrictExponent R c) ({0} : Family R) = {restrictExponent R c} := by
      simp [translatedFamily]
    rw [he]
    exact linearResolution_of_polymatroidal (singleton_polymatroidal _)

lemma shiftedPure_first (U : Finset V) (q c : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) :
    FirstNonlinear (k := k) (localFamily (translatedFamily c (pureIsolator U q)) U)
      (q.degree+(restrictExponent U c).degree) (q.support.card-1) := by
  rw [localFamily_translated, pureIsolator_local_at U q hq hsupp]
  have hcard := restrict_support_card U q hq
  have hd := restrict_degree_eq U q hq
  have H := deletedVeronese_shift_first (k := k)
    (restrictExponent U q) (restrictExponent U c) (by omega)
  rw [hcard, hd] at H
  convert H using 1
  congr <;> exact Subsingleton.elim _ _

lemma shiftedPure_local_at_degree (U : Finset V) (q c : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) :
    Equigenerated (localFamily (translatedFamily c (pureIsolator U q)) U)
      (q.degree+(restrictExponent U c).degree) := by
  rw [localFamily_translated, pureIsolator_local_at U q hq hsupp]
  simpa only [restrict_degree_eq U q hq] using translatedFamily_equigenerated
    (deletedVeronese_equigenerated (restrictExponent U q)) (restrictExponent U c)

lemma shiftedPure_unique_bad (U : Finset V) (q c : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) (R : Finset V) :
    HasLinearResolution (monomialIdeal k (localFamily (translatedFamily c (pureIsolator U q)) R))
      ↔ R ≠ U := by
  constructor
  · intro h he
    subst R
    exact firstNonlinear_not_linear
      (localFamily_nonempty (translatedFamily_nonempty (pureIsolator_nonempty U q hq hsupp) c) U)
      (shiftedPure_local_at_degree U q c hq hsupp) (shiftedPure_first U q c hq hsupp) h
  · exact shiftedPure_local_linear U R q c hq hsupp

lemma mixedIsolator_unique_bad (U : Finset V) (a b : V) (ha : a ∈ U) (hb : b ∈ U)
    (hab : a ≠ b) (hT : Uᶜ.Nonempty) (R : Finset V) :
    HasLinearResolution (monomialIdeal k (localFamily (pureIsolator U (Finsupp.single a 1)) R))
      ↔ R ≠ U := by
  constructor
  · rintro ⟨d, ⟨P⟩⟩ he
    subst R
    rw [mixedIsolator_local_at U a ha hT] at P
    exact mixedCore_not_equigenerated (⟨a, ha⟩ : U) ⟨b, hb⟩
      (fun he => hab (congrArg Subtype.val he))
      ⟨d, LinearResolution.equigenerated_of_monomial _ (mixedCore_antichain _) P⟩
  · exact mixedIsolator_local_linear U R a ha hT

end Characterizations.Isolators
