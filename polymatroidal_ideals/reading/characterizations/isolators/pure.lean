import Characterizations.Isolators.Projection
import Characterizations.Strands.DeletedGenerators

/-! # The exact family isolating one nonlinear localization -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma singleton_polymatroidal (a : Exponent V) : IsPolymatroidal ({a} : Family V) := by
  refine ⟨⟨a.degree, fun b hb => by simpa using congrArg Finsupp.degree (mem_singleton.mp hb)⟩, ?_⟩
  intro b hb c hc i hi
  have hb' := mem_singleton.mp hb
  have hc' := mem_singleton.mp hc
  subst b; subst c
  exact False.elim (lt_irrefl _ hi)

lemma purePower_mem (T : Finset V) (h : Exponent V) (hsupp : 2 ≤ h.support.card)
    (i : V) (hi : i ∉ T) : Finsupp.single i h.degree ∈ deletedBounded h.degree T h := by
  apply (mem_deletedBounded _ _ _ _).mpr
  refine ⟨?_, Finsupp.degree_single _ _, ?_⟩
  · obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (show 1 < h.support.card by omega) i
    intro he
    have hh := congrArg (fun a : Exponent V => a j) he
    have hjp : h j ≠ 0 := Finsupp.mem_support_iff.mp hj
    simp [Finsupp.single_apply, hji, hji.symm] at hh
    exact hjp hh.symm
  · intro j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp [Finsupp.single_apply, hji, hji.symm]

lemma localFamily_eq_zero_of_purePower (T R : Finset V) (h : Exponent V)
    (hsupp : 2 ≤ h.support.card) (i : V) (hiT : i ∉ T) (hiR : i ∉ R) :
    localFamily (deletedBounded h.degree T h) R = {0} := by
  apply minimalFamily_eq_of_divisors _ {0}
    (singleton_polymatroidal (0 : Exponent R)).1.choose_spec.antichain
  · intro a ha
    have he : a = 0 := mem_singleton.mp ha
    subst a
    refine mem_image.mpr ⟨Finsupp.single i h.degree, purePower_mem T h hsupp i hiT, ?_⟩
    ext j
    have hji : j.val ≠ i := fun he => hiR (he ▸ j.property)
    simp [restrictExponent_apply, Finsupp.single_apply, hji, hji.symm]
  · intro a ha
    exact ⟨0, mem_singleton_self _, bot_le⟩

lemma deletedBounded_linearResolution {k : Type u} [CommRing k] [Nontrivial k]
    (d : ℕ) (T : Finset V) (h : Exponent V) (hsat : ∀ i ∈ T, h i = 1)
    (hT : T.Nonempty) : Nonempty (LinearResolution (monomialIdeal k (deletedBounded d T h)) d) := by
  obtain ⟨w, hw⟩ := hT
  obtain ⟨o, ho⟩ := exists_lastVariable w
  exact linearResolution_of_linearQuotients _ d (deletedBounded_equigenerated d T h)
    (variableRevlex o) (variableRevlex_irrefl o) (fun {_ _ _} => variableRevlex_trans o)
    (variableRevlex_total o) (deletedBounded_linearQuotients_last d T h hsat o w hw ho)

def removedExponent (U : Finset V) (q : Exponent V) := q + indicatorExponent Uᶜ

def pureIsolator (U : Finset V) (q : Exponent V) : Family V :=
  deletedBounded (removedExponent U q).degree Uᶜ (removedExponent U q)

lemma removedExponent_saturated (U : Finset V) (q : Exponent V) (hq : q.support ⊆ U) :
    ∀ i ∈ Uᶜ, removedExponent U q i = 1 := by
  intro i hi
  have hqi : q i = 0 := Finsupp.notMem_support_iff.mp (fun h => (mem_compl.mp hi) (hq h))
  simp [removedExponent, hqi, hi]

lemma support_restrict_removed (U R : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hUR : U ⊆ R) (hsupp : 2 ≤ q.support.card) :
    2 ≤ (restrictExponent R (removedExponent U q)).support.card := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < q.support.card by omega)
  let a' : R := ⟨a, hUR (hq ha)⟩
  let b' : R := ⟨b, hUR (hq hb)⟩
  have ha' : a' ∈ (restrictExponent R (removedExponent U q)).support := by
    apply Finsupp.mem_support_iff.mpr
    have hp : 0 < q a := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha)
    simp only [restrictExponent_apply, removedExponent, Finsupp.add_apply, a']
    omega
  have hb' : b' ∈ (restrictExponent R (removedExponent U q)).support := by
    apply Finsupp.mem_support_iff.mpr
    have hp : 0 < q b := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hb)
    simp only [restrictExponent_apply, removedExponent, Finsupp.add_apply, b']
    omega
  have hab' : a' ≠ b' := fun he => hab (congrArg Subtype.val he)
  exact (Finset.one_lt_card.mpr ⟨a', ha', b', hb', hab'⟩)

lemma removed_support (U : Finset V) (q : Exponent V) (hsupp : 2 ≤ q.support.card) :
    2 ≤ (removedExponent U q).support.card := by
  apply hsupp.trans
  apply card_le_card
  intro i hi
  apply Finsupp.mem_support_iff.mpr
  have hp : 0 < q i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  simp only [removedExponent, Finsupp.add_apply]
  omega

lemma pureIsolator_degree (U : Finset V) (q : Exponent V) :
    Equigenerated (pureIsolator U q) (q.degree + Uᶜ.card) := by
  simpa [pureIsolator, removedExponent, map_add] using
    deletedBounded_equigenerated (removedExponent U q).degree Uᶜ (removedExponent U q)

lemma pureIsolator_nonempty (U : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) : (pureIsolator U q).Nonempty := by
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < q.support.card by omega)
  exact ⟨_, purePower_mem Uᶜ _ (removed_support U q hsupp) i (by simpa using hq hi)⟩

/-- Every localization omitting an uncapped variable is literally the unit family. -/
theorem pureIsolator_local_omit (U R : Finset V) (q : Exponent V)
    (hsupp : 2 ≤ q.support.card) (hUR : ¬ U ⊆ R) :
    localFamily (pureIsolator U q) R = {0} := by
  obtain ⟨i, hiU, hiR⟩ := not_subset.mp hUR
  exact localFamily_eq_zero_of_purePower Uᶜ R _ (removed_support U q hsupp) i (by simpa using hiU) hiR

/-- At every retained superset the displayed deleted capped family is exact. -/
theorem pureIsolator_local_contain (U R : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) (hUR : U ⊆ R) :
    localFamily (pureIsolator U q) R =
      deletedBounded (restrictExponent R (removedExponent U q)).degree
        (retainedCaps Uᶜ R) (restrictExponent R (removedExponent U q)) := by
  apply localFamily_deletedBounded Uᶜ R _ (removedExponent_saturated U q hq)
    (compl_subset_compl.mpr hUR) (support_restrict_removed U R q hq hUR hsupp)

lemma pureIsolator_local_at (U : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) :
    localFamily (pureIsolator U q) U = deletedVeronese (restrictExponent U q) := by
  rw [pureIsolator_local_contain U U q hq hsupp le_rfl]
  have he : restrictExponent U (removedExponent U q) = restrictExponent U q := by
    ext i
    simp [removedExponent, i.property]
  have hc : retainedCaps Uᶜ U = ∅ := by ext i; simp [i.property]
  rw [he, hc]
  rfl

/-- All localizations of the pure isolator have one generator degree. -/
theorem pureIsolator_locallyEquigenerated (U : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) : LocallyEquigenerated (pureIsolator U q) := by
  rw [locallyEquigenerated_iff]
  intro R
  by_cases hUR : U ⊆ R
  · rw [pureIsolator_local_contain U R q hq hsupp hUR]
    exact ⟨_, deletedBounded_equigenerated _ _ _⟩
  · rw [pureIsolator_local_omit U R q hsupp hUR]
    exact (singleton_polymatroidal (0 : Exponent R)).1

/-- Every localization other than the designated one has an actual linear free resolution. -/
theorem pureIsolator_local_linear {k : Type u} [CommRing k] [Nontrivial k]
    (U R : Finset V) (q : Exponent V) (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card)
    (hRU : R ≠ U) : HasLinearResolution (monomialIdeal k (localFamily (pureIsolator U q) R)) := by
  by_cases hUR : U ⊆ R
  · rw [pureIsolator_local_contain U R q hq hsupp hUR]
    refine ⟨_, deletedBounded_linearResolution _ _ _ ?_ ?_⟩
    · intro i hi
      exact removedExponent_saturated U q hq i.val ((mem_retainedCaps _ _ _).mp hi)
    · have hex : ∃ i ∈ R, i ∉ U := by
        by_contra hn
        push_neg at hn
        exact hRU (le_antisymm hn hUR)
      obtain ⟨i, hiR, hiU⟩ := hex
      exact ⟨⟨i, hiR⟩, by simp [hiU]⟩
  · rw [pureIsolator_local_omit U R q hsupp hUR]
    exact linearResolution_of_polymatroidal (singleton_polymatroidal (0 : Exponent R))

end Characterizations.Isolators
