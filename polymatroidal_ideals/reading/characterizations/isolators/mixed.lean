import Characterizations.Isolators.Pure
import Characterizations.Resolution.Degree

/-! # The lower-degree isolator with exactly one mixed-degree localization -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def mixedCore (a : V) : Family V :=
  (univ.erase a).image (fun j => Finsupp.single j 1) ∪ {Finsupp.single a 2}

@[simp] lemma mem_mixedCore (a : V) (b : Exponent V) :
    b ∈ mixedCore a ↔ (∃ j, j ≠ a ∧ b = Finsupp.single j 1) ∨ b = Finsupp.single a 2 := by
  simp [mixedCore, eq_comm, or_comm]

lemma mixedCore_antichain (a : V) : Antichain (mixedCore a) := by
  intro b hb c hc hbc
  rcases (mem_mixedCore a b).mp hb with ⟨j, hja, rfl⟩ | rfl <;>
    rcases (mem_mixedCore a c).mp hc with ⟨i, hia, rfl⟩ | rfl
  · by_cases hji : j = i
    · exact congrArg (fun j => Finsupp.single j 1) hji
    · have hh := hbc j
      simp [Finsupp.single_apply, hji, Ne.symm hji] at hh
  · have hh := hbc j
    simp [Finsupp.single_apply, hja, hja.symm] at hh
  · have hh := hbc a
    simp [Finsupp.single_apply, hia, hia.symm] at hh
  · rfl

lemma mixedCore_contains (a : V) (b : Exponent V) :
    Contains (mixedCore a) b ↔ b ≠ 0 ∧ b ≠ Finsupp.single a 1 := by
  constructor
  · rintro ⟨c, hc, hcb⟩
    rcases (mem_mixedCore a c).mp hc with ⟨j, hja, rfl⟩ | rfl
    · constructor
      · intro he; subst b; have hh := hcb j; simp at hh
      · intro he; subst b; have hh := hcb j; simp [Finsupp.single_apply, hja, hja.symm] at hh
    · constructor
      · intro he; subst b; have hh := hcb a; simp at hh
      · intro he; subst b; have hh := hcb a; simp at hh
  · rintro ⟨hb0, hba⟩
    by_cases hex : ∃ j, j ≠ a ∧ 0 < b j
    · obtain ⟨j, hja, hj⟩ := hex
      refine ⟨Finsupp.single j 1, (mem_mixedCore _ _).mpr (Or.inl ⟨j, hja, rfl⟩), ?_⟩
      intro i
      by_cases hij : i = j
      · subst i; simpa only [Finsupp.single_eq_same] using Nat.succ_le_of_lt hj
      · simp [Finsupp.single_apply, hij, Ne.symm hij]
    · have hz : ∀ j, j ≠ a → b j = 0 := by
        intro j hj
        by_contra hn
        exact hex ⟨j, hj, Nat.pos_of_ne_zero hn⟩
      have he : b = Finsupp.single a (b a) := by
        ext j
        by_cases hj : j = a
        · subst j; simp
        · rw [hz j hj, Finsupp.single_eq_of_ne hj]
      have htwo : 2 ≤ b a := by
        have h0 : b a ≠ 0 := by intro h; exact hb0 (by simpa [h] using he)
        have h1 : b a ≠ 1 := by intro h; exact hba (by simpa [h] using he)
        omega
      refine ⟨Finsupp.single a 2, (mem_mixedCore _ _).mpr (Or.inr rfl), ?_⟩
      rw [he]
      exact Finsupp.single_le_single.mpr htwo

lemma mixedCore_not_equigenerated (a b : V) (hab : a ≠ b) :
    ¬ ∃ d, Equigenerated (mixedCore a) d := by
  rintro ⟨d, hd⟩
  have h1 := hd (Finsupp.single b 1) ((mem_mixedCore _ _).mpr (Or.inl ⟨b, hab.symm, rfl⟩))
  have h2 := hd (Finsupp.single a 2) ((mem_mixedCore _ _).mpr (Or.inr rfl))
  simp only [Finsupp.degree_single] at h1 h2
  omega

lemma support_card_two_of_coordinates (h : Exponent V) (a b : V)
    (hab : a ≠ b) (ha : 0 < h a) (hb : 0 < h b) : 2 ≤ h.support.card := by
  exact Finset.one_lt_card.mpr ⟨a, Finsupp.mem_support_iff.mpr (Nat.ne_of_gt ha),
    b, Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hb), hab⟩

lemma mixed_removed_support (U : Finset V) (a : V) (ha : a ∈ U) (hT : Uᶜ.Nonempty) :
    2 ≤ (removedExponent U (Finsupp.single a 1)).support.card := by
  obtain ⟨v, hv⟩ := hT
  have hav : a ≠ v := fun he => (mem_compl.mp hv) (he ▸ ha)
  apply support_card_two_of_coordinates _ a v hav
  · simp [removedExponent, ha]
  · simp [removedExponent, Finsupp.single_apply, hav, hav.symm, hv]

/-- The mixed core occurs literally in the retained-variable polynomial ring. -/
theorem mixedIsolator_local_at (U : Finset V) (a : V) (ha : a ∈ U)
    (hT : Uᶜ.Nonempty) :
    localFamily (pureIsolator U (Finsupp.single a 1)) U = mixedCore (⟨a, ha⟩ : U) := by
  let a' : U := ⟨a, ha⟩
  let h := removedExponent U (Finsupp.single a 1)
  have hsat : ∀ i ∈ Uᶜ, h i = 1 := removedExponent_saturated U (Finsupp.single a 1) (by simpa)
  have hres : restrictExponent U h = Finsupp.single a' 1 := by
    ext i
    simp [h, removedExponent, a', Finsupp.single_apply, Subtype.ext_iff, i.property]
  have hdeg : h.degree = 1 + Uᶜ.card := by simp [h, removedExponent, map_add]
  change minimalFamily ((deletedBounded h.degree Uᶜ h).image (restrictExponent U)) = mixedCore a'
  apply minimalFamily_eq_of_divisors _ _ (mixedCore_antichain a')
  · intro b hb
    rcases (mem_mixedCore a' b).mp hb with ⟨j, hja, rfl⟩ | rfl
    · let x := extendExponent U (Finsupp.single j 1) + indicatorExponent Uᶜ
      have hxres : restrictExponent U x = Finsupp.single j 1 := restrict_lift _ _
      refine mem_image.mpr ⟨x, (mem_deletedBounded _ _ _ _).mpr ⟨?_, ?_, ?_⟩, hxres⟩
      · intro he
        have hh := hxres.symm.trans ((congrArg (restrictExponent U) he).trans hres)
        exact hja (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) hh)
      · simp [x, map_add, extendExponent_degree, hdeg]
      · intro i hi
        have hiU : i ∉ U := mem_compl.mp hi
        simp [x, extendExponent_apply, hiU, hi]
    · obtain ⟨v, hv⟩ := hT
      let x := extendExponent U (Finsupp.single a' 2) + indicatorExponent (Uᶜ.erase v)
      have hxres : restrictExponent U x = Finsupp.single a' 2 := by
        ext i
        simp [x, extendExponent_apply, i.property]
      refine mem_image.mpr ⟨x, (mem_deletedBounded _ _ _ _).mpr ⟨?_, ?_, ?_⟩, hxres⟩
      · intro he
        have hh := congrArg (fun z : Exponent U => z a') (hxres.symm.trans ((congrArg (restrictExponent U) he).trans hres))
        simp at hh
      · have hc : 0 < Uᶜ.card := card_pos.mpr ⟨v, hv⟩
        simp only [x, map_add, extendExponent_degree, Finsupp.degree_single, indicatorExponent_degree,
          card_erase_of_mem hv, hdeg]
        omega
      · intro i hi
        have hiU : i ∉ U := mem_compl.mp hi
        simp only [x, Finsupp.add_apply, extendExponent_apply, dif_neg hiU, zero_add,
          indicatorExponent_apply]
        split_ifs <;> omega
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    obtain ⟨hxne, hxdeg, hxcap⟩ := (mem_deletedBounded _ _ _ _).mp hx
    apply (mixedCore_contains _ _).mpr
    have hsplit := degree_split U x
    have hsum : subsetSum x Uᶜ ≤ Uᶜ.card := by
      calc
        _ ≤ ∑ i ∈ Uᶜ, 1 := sum_le_sum (fun i hi => hxcap i hi)
        _ = _ := by simp
    constructor
    · intro he
      have he' := congrArg Finsupp.degree he
      simp only [map_zero] at he'
      omega
    · intro he
      apply hxne
      apply eq_of_le_of_degree_eq ?_ hxdeg
      intro i
      by_cases hiU : i ∈ U
      · have hh := congrArg (fun z : Exponent U => z ⟨i, hiU⟩) (he.trans hres.symm)
        exact hh.le
      · rw [hsat i (mem_compl.mpr hiU)]
        exact hxcap i (mem_compl.mpr hiU)

lemma mixedIsolator_local_linear {k : Type u} [CommRing k] [Nontrivial k]
    (U R : Finset V) (a : V) (ha : a ∈ U) (hT : Uᶜ.Nonempty) (hRU : R ≠ U) :
    HasLinearResolution (monomialIdeal k (localFamily (pureIsolator U (Finsupp.single a 1)) R)) := by
  let h := removedExponent U (Finsupp.single a 1)
  by_cases hUR : U ⊆ R
  · obtain ⟨v, hvR, hvU⟩ : ∃ v ∈ R, v ∉ U := by
      by_contra hn
      push_neg at hn
      exact hRU (le_antisymm hn hUR)
    let a' : R := ⟨a, hUR ha⟩
    let v' : R := ⟨v, hvR⟩
    have hav : a ≠ v := fun he => hvU (he ▸ ha)
    have hsupp : 2 ≤ (restrictExponent R h).support.card := by
      apply support_card_two_of_coordinates _ a' v' (fun he => hav (congrArg Subtype.val he))
      · simp [h, removedExponent, a', ha]
      · simp [h, removedExponent, v', Finsupp.single_apply, hav, hav.symm, hvU]
    have hsat := removedExponent_saturated U (Finsupp.single a 1) (by simpa)
    rw [show pureIsolator U (Finsupp.single a 1) = deletedBounded h.degree Uᶜ h from rfl,
      localFamily_deletedBounded Uᶜ R h hsat (compl_subset_compl.mpr hUR) hsupp]
    refine ⟨_, deletedBounded_linearResolution _ _ _ ?_ ⟨v', by simp [v', hvU]⟩⟩
    intro i hi
    exact hsat i.val ((mem_retainedCaps _ _ _).mp hi)
  · obtain ⟨i, hiU, hiR⟩ := not_subset.mp hUR
    rw [show localFamily (pureIsolator U (Finsupp.single a 1)) R = {0} from
      localFamily_eq_zero_of_purePower Uᶜ R h (mixed_removed_support U a ha hT) i (by simpa using hiU) hiR]
    exact linearResolution_of_polymatroidal (singleton_polymatroidal (0 : Exponent R))

end Characterizations.Isolators
